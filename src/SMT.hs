{-# LANGUAGE TemplateHaskell #-} 
{-# LANGUAGE MultiParamTypeClasses #-} 
{-# LANGUAGE GeneralizedNewtypeDeriving #-} 
{-# LANGUAGE ScopedTypeVariables #-} 
module SMT where
import AST
import Data.List
import Control.Monad
import Data.Maybe
import System.Process
import Control.Lens
import Data.Default (Default, def)
import qualified Data.List as L
import qualified Data.Set as S
import Control.Monad.Except
import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map.Strict as M
import qualified Data.Map.Ordered as OM
import Control.Lens
import Prettyprinter
import LabelChecking
import TypingBase
import SMTBase
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

smtSetup :: Sym ()
smtSetup = do
            emitComment $ "SMT SETUP for typing query"
            smtPrelude
            setupAllFuncs 
            setupIndexEnv
            setupNameEnv
            smtLabelSetup 
            setupTyEnv 
            emitFuncAxioms

smtTypingQuery = fromSMT smtSetup

setupIndexEnv :: Sym ()
setupIndexEnv = do
    inds <- view $ inScopeIndices
    assocs <- forM (map fst inds) $ \i -> do
        x <- freshIndexVal (show i)
        return (i, x)
    symIndexEnv .= M.fromList assocs

sLength :: SExp -> SExp
sLength e = SApp [SAtom "length", e]

sPlus :: SExp -> SExp -> SExp
sPlus e1 e2 = SApp [SAtom "plus", e1, e2]

sZero :: SExp
sZero = SAtom "zero"

setupNameEnv :: Sym ()
setupNameEnv = do
    nE <- liftCheck $ collectNameEnv
    assocs <- forM nE $ \(n, o) -> do 
        ((is1, is2), ntLclsOpt) <- liftCheck $ unbind o
        let ntOpt = case ntLclsOpt of
                    Nothing -> Nothing -- liftCheck $ typeError $ ErrNameStillAbstract n
                    Just (nt', _) -> Just nt'
        let ar = length is1 + length is2
        let sname = SAtom $ "%name_" ++ (smtName n) 
        emit $ SApp [SAtom "declare-fun", sname, SApp (replicate ar (indexSort)), nameSort]
        -- Length axiom
        emitComment $ "Length axiom for " ++ smtName n
        l <- case ntOpt of 
            Nothing -> symLenConst $ smtName n
            Just nt -> nameTypeLength nt
        is <- forM [1..ar] $ \_ -> freshSMTIndexName
        emitAssertion $ sForall 
            (map (\i -> (SAtom i, indexSort)) is) 
            (sEq (sLength $ sValue $ sBaseName sname (map SAtom is)) l) 
            [sLength $ sValue $ sBaseName sname (map SAtom is)]
        -- Disjointness from constants
        emitComment $ "Disjointness from constants for " ++ (smtName n)
        fi <- use funcInterps
        let constants = map fst $ filter (\p -> snd p == 0) $ M.elems fi
        emitAssertion $ sForall (map (\i -> (SAtom i, indexSort)) is) 
         (sAnd $ map (\f -> sNot $ sEq (sValue $ sBaseName sname (map SAtom is)) f) constants)
         [(sBaseName sname (map SAtom is))]
        return (smtName n, sname)
    -- Disjointness across names 
    emitComment $ "Disjointness across names"
    when (not $ null nE) $ do
        let different_pairs = [(x, y) | (x : ys) <- tails nE, y <- ys]
        forM_ different_pairs $ \((n1, o1), (n2, o2)) -> do
            ((is1, is2), _) <- liftCheck $ unbind o1
            ((is1', is2'), _) <- liftCheck $ unbind o2
            let ar1 = length is1 + length is2
            let ar2 = length is1' + length is2'
            emitComment $ "Disjointness " ++ smtName n1 ++ " <-> " ++ smtName n2
            ivs1' <- forM [1..ar1] $ \_ -> freshSMTIndexName
            ivs2' <- forM [1..ar2] $ \_ -> freshSMTIndexName
            let ivs1 = map SAtom ivs1'
            let ivs2 = map SAtom ivs2'
            let v1 = sValue $ sBaseName (SAtom $ "%name_" ++ smtName n1) (take ar1 ivs1)
            let v2 = sValue $ sBaseName (SAtom $ "%name_" ++ smtName n2) (take ar2 ivs2)
            emitAssertion $ sForall (map (\i -> (i, indexSort)) (ivs1 ++ ivs2)) (sNot $ sEq v1 v2) [v1, v2]
    symNameEnv .= M.fromList assocs


symLenConst :: String -> Sym SExp
symLenConst s = do
    v <- lengthConstant s
    return $ SApp [SAtom "IntToBS", v]

nameTypeLength :: NameType -> Sym SExp
nameTypeLength nt = 
    symLenConst $ case nt^.val of
                    NT_Nonce -> "nonce"
                    NT_DH -> "DH"
                    NT_Enc _ -> "enckey"
                    NT_PKE _ -> "pkekey"
                    NT_Sig _ -> "sigkey"
                    NT_PRF _ -> "prfkey"
                    NT_MAC _ -> "mackey"

symNameExp :: NameExp -> Sym SExp
symNameExp ne = do
    n <- getSymName ne
    return $ SApp [SAtom "Value", n]

mkTy :: Maybe String -> Ty -> Sym SExp
mkTy s t = do
    x <- freshSMTVal (case s of
                     Nothing -> Nothing
                     Just x -> Just $ x ++ " : " ++ show (pretty t)
                  )
    c <- tyConstraints t x
    emitComment $ "ty constraint: " ++ show c
    emitAssertion c
    return x

setupTyEnv :: Sym ()
setupTyEnv = do
    vE <- view tyContext
    go vE
    where
        go [] = return ()
        go ((x, (_, t)) : xs) = do
            v <- mkTy (Just $ show x) t
            varVals %= (M.insert x v)
            go xs

setupUserFunc :: (ResolvedPath, UserFunc) -> Sym ()
setupUserFunc (s, f) =
    case f of
      StructConstructor tv -> do
        td <- liftCheck $ getTyDef (ignore def) (PRes $ PDot s tv)
        case td of
          StructDef idf -> do
              let ar = length $ snd $ unsafeUnbind idf
              setupFunc (PDot s tv, ar)
          _ -> error $ "Struct not found: " ++ show tv
      StructProjector _ proj -> setupFunc (PDot s proj, 1)
      EnumConstructor tv variant ->  do
        td <- liftCheck $ getTyDef (ignore def) (PRes $ PDot s tv)
        case td of
          EnumDef idf -> do
              let enum_map = snd $ unsafeUnbind idf 
              case lookup variant enum_map of
                Nothing -> error $ "Bad variant in SMT: " ++ show variant
                Just Nothing -> setupFunc (PDot s variant, 0)
                Just (Just _) -> setupFunc (PDot s variant, 1)
          _ -> error "Unknown enum in SMT"
      EnumTest _ variant -> setupFunc (PDot s (variant ++ "?"), 1)
      UninterpUserFunc f ar -> setupFunc (PDot s f, ar)


setupFunc :: (ResolvedPath, Int) -> Sym ()
setupFunc (s, ar) = do
    fs <- use funcInterps
    case M.lookup (smtName s) fs of
      Just _ -> error $ "Function " ++ show s ++ " already defined in SMT. " ++ show (M.keys fs)
      Nothing -> do
          emit $ SApp [SAtom "declare-fun", SAtom (smtName s), SApp (replicate ar (bitstringSort)), bitstringSort]
          funcInterps %= (M.insert (smtName s) (SAtom (smtName s), ar))

getFunc :: String -> Sym SExp
getFunc s = do
    fs <- use funcInterps
    case M.lookup s fs of
      Just (v, _) -> return v
      Nothing -> error $ "Function not in SMT: " ++ show s ++ show (M.keys fs)

getTopLevelFunc = getFunc . smtName . topLevelPath

constant :: String -> Sym SExp
constant s = do
    cs <- use constants
    case M.lookup s cs of
      Just v -> return v
      Nothing -> do 
          x <- freshSMTVal $ Just s
          constants %= (M.insert s x)
          return x

lengthConstant :: String -> Sym SExp
lengthConstant s = do
    cs <- use lengthConstants
    case M.lookup s cs of
      Just v -> return v
      Nothing -> do 
          x <- freshLengthVar $ Just s
          lengthConstants %= (M.insert s (x))
          return $ x


setupAllFuncs :: Sym ()
setupAllFuncs = do
    fncs <- view detFuncs
    mapM_ setupFunc $ map (\(k, (v, _)) -> (PDot PTop k, v)) fncs
    ufs <- liftCheck $ collectUserFuncs
    mapM_ setupUserFunc $ map (\(k, v) -> (pathPrefix k, v)) ufs 

    -- Verification-oriented funcs, none are unary
    emit $ SApp [SAtom "declare-fun", SAtom "EnumVal", SApp [bitstringSort], bitstringSort]
    emit $ SApp [SAtom "declare-fun", SAtom "StringToBS", SApp [SAtom "String"], bitstringSort]
    emit $ SApp [SAtom "declare-fun", SAtom "BSToString", SApp [bitstringSort], SAtom "String"]
    emitRaw $ "(assert (forall ((x String)) (! (= (BSToString (StringToBS x)) x) :pattern (StringToBS x))))"
    emit $ SApp [SAtom "declare-fun", SAtom "IndexToBS", SApp [indexSort], bitstringSort]
    emit $ SApp [SAtom "declare-fun", SAtom "BSToIndex", SApp [bitstringSort], indexSort]
    emitRaw $ "(assert (forall ((x Index)) (! (= (BSToIndex (IndexToBS x)) x) :pattern (IndexToBS x))))"
    emit $ SApp [SAtom "declare-fun", SAtom "IntToBS", SApp [SAtom "Int"], bitstringSort]
    emit $ SApp [SAtom "declare-fun", SAtom "BSToInt", SApp [bitstringSort], SAtom "Int"]
    emitRaw $ "(assert (forall ((x Int)) (! (=> (>= x 0) (= (BSToInt (IntToBS x)) x)) :pattern (IntToBS x))))"
    emitRaw $ "(assert (forall ((x Int) (y Int)) (! (= (plus (IntToBS x) (IntToBS y)) (IntToBS (+ x y))) :pattern (plus (IntToBS x) (IntToBS y)))))"
    emitRaw $ "(assert (forall ((x Int) (y Int)) (! (= (mult (IntToBS x) (IntToBS y)) (IntToBS (* x y))) :pattern (mult (IntToBS x) (IntToBS y)))))"
    emitRaw $ "(assert (= (BSToInt zero) 0))"
    emitRaw $ "(assert (= (IntToBS 0) zero))"
    return ()



tyConstraints :: Ty -> SExp -> Sym SExp
tyConstraints t v = do
    liftCheck $ debug $ pretty "tyConstraints for " <> pretty t
    case t^.val of
      (TData _ _) -> return $ sTrue
      (TDataWithLength _ a) -> do
          va <- interpretAExp a
          return $ (sLength v) `sEq` va
      TBool _ -> do
          let t = bTrue
          let f = bFalse
          return $ (v `sEq` t) `sOr` (v `sEq` f)
      TRefined t xp -> do
          (x, p) <- liftCheck $ unbind xp
          v1 <- tyConstraints t v
          vE <- use varVals
          varVals %= (M.insert x v)
          v2 <- interpretProp p
          varVals .= vE
          return $ SApp [SAtom "and", v1, v2]
      TOption t -> do
          b <- tyConstraints t v
          nb <- constant "none"
          return $ (v `sEq` nb) `sOr` ((sNot $ v `sEq` nb) `sAnd2` b)
      TName n -> do
          nt <- liftCheck $ getNameType n
          lv <- nameTypeLength nt
          v' <- symNameExp n
          return $ (v `sEq` v') `sAnd2` ((sLength v) `sEq` lv)
      (TVK n) -> do
        nv <- symNameExp n
        vk <- getTopLevelFunc ("vk")
        return $ v `sEq` (SApp [vk, nv])
      (TDH_PK n) -> do
        nv <- symNameExp n
        pk <- getTopLevelFunc ("dhpk")
        return $ v `sEq` (SApp [pk, nv])
      (TSS n m) -> do
        nv <- symNameExp n
        mv <- symNameExp m
        pk <- getTopLevelFunc ("dhpk")
        f <- getTopLevelFunc ("dh_combine")
        return $ v `sEq` (SApp [f, SApp [pk, nv], mv])
      (TEnc_PK n) -> do
        nv <- symNameExp n
        pk <- getTopLevelFunc ("enc_pk") 
        return $ v `sEq` (SApp [pk, nv])
      TUnit -> do
          let b = unit
          return $ v `sEq` b
      TAdmit -> return sTrue
      TUnion t1 t2 -> do
          c1 <- tyConstraints t1 v
          c2 <- tyConstraints t2 v
          return $ sOr c1 c2
      TConst s@(PRes (PDot pth _)) ps -> do
          td <- liftCheck $ getTyDef (t^.spanOf) s
          case td of
            TyAbstract -> return sTrue
            TyAbbrev t -> tyConstraints t v
            StructDef ixs -> do
                dts <- liftCheck $ extractStruct (t^.spanOf) ps (show s) ixs
                let v' = SApp $ (SAtom (smtName s) : map (\(d, _) -> SApp [SAtom $ smtName $ PDot pth d, v]) dts)
                let ext_ax = sEq v v' -- Extensionality axiom
                let length_ax = sEq (sLength v) $ foldr sPlus sZero $ map sLength $ map (\(d, _) -> SApp [SAtom $ smtName $ PDot pth d, v]) dts
                ty_axioms <- forM dts $ \(d, t) -> tyConstraints t (SApp [SAtom $ smtName $ PDot pth d, v])
                return $ sAnd (ext_ax : length_ax : ty_axioms)
            EnumDef b -> do
                bdy <- liftCheck $ extractEnum (t^.spanOf) ps (show s) b
                let val = SApp [SAtom "EnumVal", v]
                cases <- forM [0 .. (length bdy - 1)] $ \i -> do
                    c <- tyConstraints (case snd $ bdy !! i of
                                          Just t -> t
                                          Nothing -> tUnit
                                       ) val
                    fconstr <- getFunc $ smtName $ PDot pth $ fst $ bdy !! i
                    ftest <- getFunc $ smtName $ PDot pth $ (fst $ bdy !! i) ++ "?"
                    let vEq = case (snd $ bdy !! i) of
                          Just _ -> sEq v (SApp [fconstr, val])
                          Nothing -> sTrue
                    return $ sAnd [vEq, (sEq (SApp [ftest, v]) bTrue), c]
                ftests <- mapM (\(n, _) -> getFunc $ smtName $ PDot pth $ n ++ "?") bdy
                return $ (SApp $ [SAtom "or"] ++ cases) `sAnd2` (enumDisjConstraint ftests v)
      TCase tc t1 t2 -> do
          c1 <- tyConstraints t1 v
          c2 <- tyConstraints t2 v
          sc <- interpretProp tc
          return $ sAnd2 (sImpl sc c1) (sImpl (sNot sc) c2)
      TExistsIdx _ -> return sTrue -- Opaque to SMT


-- Get length of ty, which needs to be statically known
tyLen :: Ty -> Sym SExp
tyLen t = do
    case t^.val of 
      TName n -> do
          nt <- liftCheck $ getNameType n
          nameTypeLength nt
      _ -> liftCheck $ typeError (t^.spanOf) $ show $ pretty "unimp: tyLen for " <> pretty t

interpretAExp :: AExpr -> Sym SExp
interpretAExp ae = 
    case ae^.val of
      AEVar _ x -> do
        env <- use varVals
        case M.lookup x env of 
            Just v -> return v
            Nothing -> error $ "SMT ERROR : Cannot find " ++ show x ++ " with varVals " ++ show (pretty (M.keys env))
      AEApp f _ xs -> do
        vs <- mapM interpretAExp xs
        case f of
          -- Special cases
          f | f == (topLevelPath "UNIT") -> return unit
          f | f == (topLevelPath "true") -> return bTrue
          f | f == (topLevelPath "false") -> return bFalse
          _ -> do
              vf <- getFunc $ smtName f
              return $ sApp vf vs
      AEString s -> return $ SApp [SAtom "StringToBS", SAtom $ "\"" ++ s ++ "\""]
      AELenConst s -> symLenConst s
      AEInt i -> return $ SApp [SAtom "IntToBS", SAtom (show i)]
      AEGet ne -> do
          liftCheck $ debug $ pretty "Evaluating get" <+> parens (pretty ne)
          symNameExp ne
      AEGetEncPK ne -> interpretAExp $ aeApp (topLevelPath  "enc_pk") [] [mkSpanned $ AEGet ne]
      AEGetVK ne -> interpretAExp $ aeApp (topLevelPath  "vk") [] [mkSpanned $ AEGet ne]
      AEPackIdx i a -> interpretAExp a


bTrue :: SExp
bTrue = SAtom "TRUE"

bFalse :: SExp
bFalse = SAtom "FALSE"

unit :: SExp
unit = SAtom "UNIT"

interpretProp :: Prop -> Sym SExp
interpretProp p = 
    case p^.val of
      PTrue -> return sTrue
      PFalse -> return sFalse
      (PAnd p1 p2) -> 
        liftM2 (sAnd2) (interpretProp p1) (interpretProp p2)
      (POr p1 p2) ->
        liftM2 (sOr) (interpretProp p1) (interpretProp p2)
      (PImpl p1 p2) ->
        liftM2 (sImpl) (interpretProp p1) (interpretProp p2)
      (PNot p) ->
        sNot <$> interpretProp p
      (PEq p1 p2) ->
        liftM2 (sEq) (interpretAExp p1) (interpretAExp p2)
      (PEqIdx i1 i2) ->
        liftM2 (sEq) (symIndex i1) (symIndex i2)
      (PHappened s (id1, id2) xs) -> do
          vs <- mapM interpretAExp xs
          ivs <- mapM symIndex id1
          ivs' <- mapM symIndex id2
          return $ SApp $ [SAtom "Happened", SAtom ("\"" ++ smtName s ++ "\""), mkIdxList (ivs ++ ivs'), mkBSList vs]
      (PFlow l1 l2 ) -> do
        liftCheck $ debug $ pretty "Interpreting prop " <> pretty l1 <+> pretty "<=" <+> pretty l2
        x <- symLbl l1
        y <- symLbl l2
        return $ SApp [SAtom "Flows", x, y]
         
mkBSList :: [SExp] -> SExp
mkBSList [] = SAtom "BSListNil"
mkBSList (x:xs) = SApp [SAtom "BSListCons", x, mkBSList xs]

mkIdxList :: [SExp] -> SExp
mkIdxList [] = SAtom "IdxListNil"
mkIdxList (x:xs) = SApp [SAtom "IdxListCons", x, mkIdxList xs]

emitFuncAxioms :: Sym () 
emitFuncAxioms = do
    -- true <> false <> ()
    let tt = unit
    let t = bTrue
    let f = bFalse
    emitAssertion $ sDistinct [tt, t, f]

    -- eq(x,y) = true ==> x = y
    eqf <- getTopLevelFunc "eq"
    emitAssertion $ sForall [(SAtom "x", bitstringSort), (SAtom "y", bitstringSort)] ((sEq (SApp [eqf, SAtom "x", SAtom "y"]) t) `sImpl` (sEq (SAtom "x") (SAtom "y"))) [(SApp [eqf, SAtom "x", SAtom "y"])]
    -- eq(x,y) = false ==> x != y
    emitAssertion $ sForall [(SAtom "x", bitstringSort), (SAtom "y", bitstringSort)] ((sEq (SApp [eqf, SAtom "x", SAtom "y"]) f) `sImpl` (sNot $ sEq (SAtom "x") (SAtom "y"))) [(SApp [eqf, SAtom "x", SAtom "y"])]

    -- andb(x, y) = true ==> x = true /\ y = true
    andbf <- getTopLevelFunc "andb"
    emitAssertion $ sForall [(SAtom "x", bitstringSort), (SAtom "y", bitstringSort)] 
        ((sEq (SApp [andbf, SAtom "x", SAtom "y"]) t) `sImpl` (sAnd2 (sEq (SAtom "x") t) (sEq (SAtom "y") t))) 
        [(SApp [andbf, SAtom "x", SAtom "y"])]

    emitComment $ "RO equality axioms"
    ros <- liftCheck $ collectRO
    let sConcat a b = SApp [SAtom "concat", a, b]
    forM_ ros $ \(s, (aes, _)) -> do
        vs <- mapM interpretAExp aes
        let v = foldr sConcat (head vs) (tail vs) 
        emitAssertion $ sEq (sValue $ sROName $ smtName s) v
    
    emitComment $ "Enum test faithful axioms"
    enumTestFaithulAxioms

enumDisjConstraint :: [SExp] -> SExp -> SExp
enumDisjConstraint fs v = 
    let range = [0 .. (length fs) - 1] in
    let ijs = [(x,y) | x <- range, y <- range, x < y] in
    sAnd $ map (\(i, j) -> sNot $ sAnd2 (sEq (SApp [fs !! i, v]) bTrue) (sEq (SApp [fs !! j, v]) bTrue)) ijs

enumTestFaithulAxioms :: Sym ()
enumTestFaithulAxioms = do
    tds <- liftCheck $ collectTyDefs
    forM_ tds $ \(pth, td) -> do
        case td of
          EnumDef m' -> do
              (_, m) <- liftCheck $ unbind m'
              forM_ m $ \(x, ot) -> do
                  fconstr <- getFunc $ smtName $ PDot (pathPrefix pth) x
                  ftest <- getFunc $ smtName $ PDot (pathPrefix pth) $  x ++ "?"
                  case ot of
                    Nothing -> 
                        emitAssertion $ sEq (SApp [ftest, fconstr]) bTrue
                    Just _ -> do
                        emitAssertion $ sForall [(SAtom "%x", bitstringSort)] (sEq (SApp [ftest, SApp [fconstr, SAtom "%x"]]) bTrue) [SApp [fconstr, SAtom "%x"]]
                        emitAssertion $ sForall [(SAtom "%x", bitstringSort)] 
                            (sOr (sEq (SApp [ftest, SAtom "%x"]) bTrue)
                                 (sEq (SApp [ftest, SAtom "%x"]) bFalse))
                            [SApp [ftest, SAtom "%x"]]
          _ -> return ()
    
subTypeCheck :: Ty -> Ty -> Sym ()
subTypeCheck t1 t2 = do
    v <- mkTy Nothing t1
    c <- tyConstraints t2 v
    emitComment $ "Checking subtype " ++ show (pretty t1) ++ " <= " ++ show (pretty t2)
    emitToProve c

--

emitDHCombineDisjoint :: Sym ()
emitDHCombineDisjoint = do
    nE <- liftCheck $ collectNameEnv 
    -- Get all DH names
    -- forall x y n1 n2, n1 <> n2 => dhcombine(x, n1) <> dhcombine(y, n2)
    dhnames' <- forM nE  $ \(x, nt) -> do
        ((ps1, ps2), ntLclsOpt') <- unbind nt
        nt' <- case ntLclsOpt' of
            Nothing -> liftCheck $ typeError (ignore def) $ show $ ErrNameStillAbstract $ show  x
            Just (nt'', _) -> return nt''
        case nt'^.val of
          NT_DH -> if length ps1 == 0 && length ps2 == 0 then return (Just x) else return Nothing
          _ -> return Nothing
    let dhnames = catMaybes dhnames'
    let sDhCombine x y = SApp [SAtom "dh_combine", SApp [SAtom "dhpk", SApp [SAtom "Value", x]], SApp [SAtom "Value", y]]
    let n1 = SAtom "n1"
    let n2 = SAtom "n2"
    let different_pairs = [(x, y) | (x : ys) <- tails dhnames, y <- ys]
    forM_ different_pairs $ \(m1, m2) -> do
        emitAssertion $ 
            sForall [(n1, nameSort), (n2, nameSort)]
                (sNot $ sEq (sDhCombine n1 (SAtom $ "%name_" ++ smtName m1)) (sDhCombine n2 (SAtom $ "%name_" ++ smtName m2)))
                [sDhCombine n1 (SAtom $ "%name_" ++ smtName m1), sDhCombine n2 (SAtom $ "%name_" ++ smtName m2)]

emitROInjectivityAxioms :: Sym ()
emitROInjectivityAxioms = do
    let sConcat a b = SApp [SAtom "concat", a, b]
    let x = SAtom "x"
    let y = SAtom "y"
    let z = SAtom "z"
    let w = SAtom "w"
    -- concat(x, y) == concat(z, w) /\ length(x) = length y ==> x = z /\ y = w
    emitAssertion $ 
        sForall [(x, bitstringSort), (y, bitstringSort), (z, bitstringSort), (w, bitstringSort)]
        (sImpl (sAnd2 (sEq (sConcat x y) (sConcat z w)) (sEq (sLength x) (sLength z)))
               (sAnd2 (sEq x z) (sEq y w)))
        [sConcat x y, sConcat z w]
    -- length(concat(x, y)) = plus(length(x), length(y))
    emitAssertion $ 
        sForall [(x, bitstringSort), (y, bitstringSort)]
         (sEq (sLength $ sConcat x y) (sPlus (sLength x) (sLength y)))
         [sConcat x y]
    -- length(y) <> 0 ==> x <> concat(x, y)
    emitAssertion $ 
        sForall [(x, bitstringSort), (y, bitstringSort)]
         (sImpl (sNot $ sEq (sLength y) sZero) (sNot $ sEq x (sConcat x y)))
         [sConcat x y]
    -- length(x) <> 0 ==> y <> concat(x, y)
    emitAssertion $ 
        sForall [(x, bitstringSort), (y, bitstringSort)]
         (sImpl (sNot $ sEq (sLength x) sZero) (sNot $ sEq y (sConcat x y)))
         [sConcat x y]
    -- dh_combine results in different values for different names
    emitComment $ "Emitting DH disjointness"
    emitDHCombineDisjoint


sConcats :: [SExp] -> SExp
sConcats vs = 
    let sConcat a b = SApp [SAtom "concat", a, b] in
    foldr sConcat (head vs) (tail vs) 





symROUnique :: [[AExpr]] -> [AExpr] -> Sym ()
symROUnique ess e = do
    emitComment $ "Proving ROUnique with es = " ++ show (pretty ess) ++ " and e = " ++ show (pretty e)
    vs <- forM ess $ \es -> do
        vs <- mapM interpretAExp es
        return $ sConcats vs
    v <- sConcats <$> mapM interpretAExp  e
    emitROInjectivityAxioms
    forM_ vs $ \v' -> 
        emitToProve $ sNot $ sEq v v' 

symListUniq :: [AExpr] -> Sym ()
symListUniq es = do
    vs <- mapM interpretAExp es
    emitComment $ "Proving symListUniq with es = " ++ show (pretty es)
    emitToProve $ sDistinct vs
    return ()

---- First AExpr is in the top level (ie, only names), second is regular
symCheckEqTopLevel :: [AExpr] -> [AExpr] -> Sym ()
symCheckEqTopLevel eghosts es = do
    if length eghosts /= length es then emitToProve sFalse else do
        vE <- use varVals
        v_es <- mapM interpretAExp es
        t_es <- liftCheck $ mapM inferAExpr es
        forM_ (zip v_es t_es) $ \(x, t) -> do
            c <- tyConstraints t x
            emitAssertion c
        varVals .= M.empty
        v_eghosts <- mapM interpretAExp eghosts
        varVals .= vE
        emitComment $ "Checking if " ++ show (pretty es) ++ " equals ghost val " ++ show (pretty eghosts) 
        emitToProve $ sAnd $ map (\(x, y) -> sEq x y) $ zip v_es v_eghosts 

symAssert :: Prop -> Sym ()
symAssert p = do
    b <- interpretProp p
    emitComment $ "Proving prop " ++ show (pretty p)
    emitToProve b

symDecideProp :: Prop -> Check (Maybe String, Maybe Bool) 
symDecideProp p = do
    b1 <- fromSMT smtSetup $ do
        emitComment $ "Trying to prove prop " ++ show (pretty p)
        b <- interpretProp p
        emitToProve b
    if snd b1 then return (fst b1, Just True) else do
        b2 <- fromSMT smtSetup $ do
            emitComment $ "Trying to prove prop " ++ show (pretty $ pNot p)
            b <- interpretProp $ pNot p
            emitToProve b
        if snd b2 then return (fst b2, Just False) else return (fst b2, Nothing)

checkFlows :: Label -> Label -> Check (Maybe String, Maybe Bool)
checkFlows l1 l2 = do
    debug $ pretty "checkFlows for " <> pretty l1 <+> pretty "and" <+> pretty l2
    b1 <- fromSMT smtSetup $ do
            emitComment $ "Trying to prove " ++ show (pretty l1) ++ " <= " ++ show (pretty l2)
            x <- symLbl l1
            y <- symLbl l2
            emitToProve $ SApp [SAtom "Flows", x, y]
    if snd b1 then return (fst b1, Just True) else do
        b2 <- fromSMT smtSetup $ do
                emitComment $ "Trying to prove " ++ show (pretty l1) ++ " !<= " ++ show (pretty l2)
                x <- symLbl l1
                y <- symLbl l2
                emitToProve $ sNot $ SApp [SAtom "Flows", x, y]
        if snd b2 then return (fst b2, Just False) else return (fst b2, Nothing)

