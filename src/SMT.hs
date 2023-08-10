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
            setupSMTOptions
            setupAllFuncs 
            setupIndexEnv
            setupNameEnvRO
            smtLabelSetup 
            setupTyEnv 

smtTypingQuery = fromSMT smtSetup

setupSMTOptions :: Sym ()
setupSMTOptions = do
    o <- view $ z3Options
    forM_ (M.assocs o) $ \(k, v) -> do
        emit $ SApp [SAtom "set-option", SAtom k, SAtom v]

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


setupNameEnvRO :: Sym ()
setupNameEnvRO = do
    dfs <- liftCheck $ collectNameDefs
    fdfs <- flattenNameDefs dfs
    -- First, declare all names
    forM_ fdfs $ \((n, oi), b) -> do
        ((is, ps), nd) <- liftCheck $ unbind b
        sn <- smtNameOfFlattenedName (n, oi)
        let ar = length is + length ps
        emit $ SApp [SAtom "declare-fun", sn, SApp (replicate ar indexSort), nameSort]
    -- Now, declare them all disjoint
    emitComment $ "Disjointness across names"
    let different_pairs = [(x, y) | (x : ys) <- tails fdfs, y <- ys]
    forM_ different_pairs $ \((noi1, b1), (noi2, b2)) -> do
        ((is1, ps1), _) <- liftCheck $ unbind b1
        sname1 <- smtNameOfFlattenedName noi1
        let ar1 = length is1 + length ps1
        let q1 = map (\i -> (SAtom $ show i, indexSort)) $ is1 ++ ps1
        let v1 = sApp $ sname1 : (map fst q1)
        ((is2, ps2), _) <- liftCheck $ unbind b2
        sname2 <- smtNameOfFlattenedName noi2
        let ar2 = length is2 + length ps2
        let q2 = map (\i -> (SAtom $ show i, indexSort)) $ is2 ++ ps2
        let v2 = sApp $ sname2 : (map fst q2)
        emitAssertion $ sForall (q1 ++ q2) (sNot $ sEq v1 v2) [v1, v2] $ "disj_" ++ show (sname1) ++ "_" ++ show (sname2) 

        when (ar1 > 0) $ do
            q12 <- forM q1 $ \_ -> do
                x <- freshSMTIndexName
                return (SAtom x, indexSort)
            let v12 = sApp $ sname1 : (map fst q12)
            let q1_eq_q12 = sAnd $ map (\i -> sEq (fst $ q1 !! i) (fst $ q12 !! i)) [0 .. (length q1 - 1)]
            let v1_eq_v12 = SApp [SAtom "=", SAtom "TRUE", SApp [SAtom "eq", SApp [SAtom "ValueOf", v1], 
                                                                             SApp [SAtom "ValueOf", v12]]]
            emitAssertion $ sForall (q1 ++ q12)
                (v1_eq_v12 `sImpl` q1_eq_q12)
                [v1_eq_v12]
                ("self_disj_" ++ show (sname1))
    -- Axioms relevant for each def 
    forM_ fdfs $ \(noi, b) -> do 
        ((is, ps), nd) <- liftCheck $ unbind b
        let ar = length is + length ps
        sname <- smtNameOfFlattenedName noi
        let ntOpt = case nd of
                      BaseDef (nt, _) -> Just nt
                      AbstractName -> Nothing
                      RODef (_, [nt]) -> Just nt
        let ivs = map (\i -> (SAtom (show i), indexSort)) (is ++ ps)
        withIndices (map (\i -> (i, IdxSession)) is ++ map (\i -> (i, IdxPId)) ps) $ do
            case ntOpt of 
              Nothing -> return ()
              Just nt -> do
                nk <- nameKindOf nt
                emitAssertion $ sForall
                    ivs
                    (SApp [SAtom "HasNameKind", sApp (sname : (map fst ivs)), nk])
                    [sApp (sname : (map fst ivs))]
                    ("nameKind_" ++ show (sname))

                let nexp = mkSpanned $ NameConst (map (IVar (ignore def)) is, map (IVar (ignore def)) ps) (PRes (fst noi)) (snd noi)
                emitComment $ "nameDefFlows for" ++ show (pretty nexp)                                
                lAxs <- nameDefFlows nexp nt
                sAxs <- forM lAxs $ \(l1, l2) -> do
                    vl1 <- symLabel l1
                    vl2 <- symLabel l2
                    return $ SApp [SAtom "Flows", vl1, vl2]
                emitAssertion $ sForall
                    ivs
                    (sAnd sAxs)
                    [sApp (sname : (map fst ivs))]
                    ("nameDefFlows_" ++ show (sname))

            case nd of
              RODef (as, _) -> do
                  emitComment $ "RO solvability for " ++ show (sApp $ sname : map fst ivs)
                  ax <- solvabilityAxioms as (sApp $ sname : (map fst ivs))
                  emitAssertion $ sForall ivs ax [sApp $ sname : (map fst ivs)] $ "RO_solvability_" ++ show (sname)

                  emitComment $ "RO mapsto axiom"
                  asv <- mapM interpretAExp as
                  let (Just i) = snd noi
                  let roAx = SApp [SAtom "RO", sConcats asv, SApp [SAtom "ValueOf", sApp $ sname : (map fst ivs)], SAtom $ show i]
                  emitAssertion $ sForall ivs roAx [] $ "RO_mapsto_" ++ show (sname)
              _ -> return ()

nameKindOf :: NameType -> Sym SExp
nameKindOf nt = 
    return $ case nt^.val of
      NT_DH -> SAtom "DHkey"
      NT_Enc _ -> SAtom "Enckey"
      NT_StAEAD _ _ _ _ -> SAtom "Enckey"
      NT_PKE _ -> SAtom "PKEkey"
      NT_Sig _ -> SAtom "Sigkey"
      NT_PRF _ -> SAtom "PRFkey"
      NT_MAC _ -> SAtom "MACkey"
      NT_Nonce -> SAtom "Nonce"

symLenConst :: String -> Sym SExp
symLenConst s = do
    v <- lengthConstant s
    return $ SApp [SAtom "I2B", v]

symNameExp :: NameExp -> Sym SExp
symNameExp ne = do
    liftCheck $ debug $ pretty "symNameExp" <+> pretty ne
    n <- getSymName ne
    return $ SApp [SAtom "ValueOf", n]

mkTy :: Maybe String -> Ty -> Sym SExp
mkTy s t = do
    x <- freshSMTVal (case s of
                     Nothing -> Nothing
                     Just x -> Just $ x ++ " : " ++ show (pretty t)
                  )
    c <- tyConstraints t x
    emitComment $ "ty constraint for " ++ show x ++ ": " ++ show (pretty t)
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

-- TODO: reinterpret in terms of their SMT semantics
setupUserFunc :: (ResolvedPath, UserFunc) -> Sym ()
setupUserFunc (s, f) =
    case f of
      StructConstructor tv -> do
        -- Concats
        td <- liftCheck $ getTyDef (ignore def) (PRes $ PDot s tv)
        case td of
          StructDef idf -> do
              let ar = length $ snd $ unsafeUnbind idf
              setupFunc (PDot s tv, ar)
          _ -> error $ "Struct not found: " ++ show tv
      StructProjector _ proj -> setupFunc (PDot s proj, 1) -- Maybe leave uninterpreted?
      EnumConstructor tv variant ->  do
        -- Concat the pair using EnumTag
        td <- liftCheck $ getTyDef (ignore def) (PRes $ PDot s tv)
        case td of
          EnumDef idf -> do
              let enum_map = snd $ unsafeUnbind idf 
              sn <- smtName (PDot s variant)
              let (i, ar) = 
                      case lookupIndex variant enum_map of
                        Nothing -> error $ "Bad variant in SMT: " ++ show variant
                        Just (i, Nothing) -> (i, 0) 
                        Just (i, Just _) -> (i, 1) 
              case ar of
                0 -> do 
                  emit $ SApp [SAtom "define-fun", SAtom sn, SApp [], 
                               SAtom "Bits", SApp [SAtom "concat", SApp [SAtom "EnumTag", SAtom $ show i], SAtom "UNIT" ]
                              ]
                  emitAssertion $ SApp [SAtom "IsConstant", SAtom sn]
                1 -> 
                  emit $ SApp [SAtom "define-fun", SAtom sn, SApp [SApp [SAtom "%x", SAtom "Bits"] ], 
                               SAtom "Bits", SApp [SAtom "concat", SApp [SAtom "EnumTag", SAtom $ show i], SAtom "%x" ]
                              ]
              funcInterps %= (M.insert sn (SAtom sn, ar))
          _ -> error "Unknown enum in SMT"
      EnumTest tv variant -> do -- Compare the first eight bits using prefix 
          td <- liftCheck $ getTyDef (ignore def) (PRes $ PDot s tv)
          case td of
            EnumDef idf -> do
                let enum_map = snd $ unsafeUnbind idf 
                let i = case lookupIndex variant enum_map of
                          Nothing -> error $ "Bad variant in SMT: " ++ show variant
                          Just (i, _) -> i
                sn <- smtName (PDot s (variant ++ "?"))
                emit $ SApp [SAtom "define-fun", SAtom sn, SApp [SApp [SAtom "%x", SAtom "Bits"] ], 
                             SAtom "Bits", SApp [SAtom "TestEnumTag", (SAtom $ show i), SAtom "%x"] ]
                funcInterps %= (M.insert sn (SAtom sn, 1))
      UninterpUserFunc f ar -> setupFunc (PDot s f, ar)

lookupIndex :: Eq a => a -> [(a, b)] -> Maybe (Int, b)
lookupIndex x xs = go 0 xs
    where
        go _ [] = Nothing
        go i ((y, z) : ys) | x == y = Just (i, z)
                           | otherwise = go (i + 1) ys

builtInSMTFuncs :: [String]
builtInSMTFuncs = ["length", "eq", "plus", "mult", "UNIT", "TRUE", "FALSE", "andb", "concat", "zero", "dh_combine", "dhpk", "is_group_elem"]

setupFunc :: (ResolvedPath, Int) -> Sym ()
setupFunc (s, ar) = do
    fs <- use funcInterps
    sn <- smtName s
    case M.lookup sn fs of
      Just _ -> error $ "Function " ++ show s ++ " already defined in SMT. " ++ show (M.keys fs)
      Nothing -> do
          when (not (sn `elem` builtInSMTFuncs)) $ do
              emit $ SApp [SAtom "declare-fun", SAtom sn, SApp (replicate ar (bitstringSort)), bitstringSort]
              when (ar == 0) $ do
                  emitAssertion $ SApp [SAtom "IsConstant", SAtom sn]
          funcInterps %= (M.insert sn (SAtom sn, ar))

getFunc :: String -> Sym SExp
getFunc s = do
    fs <- use funcInterps
    case M.lookup s fs of
      Just (v, _) -> return v
      Nothing -> error $ "Function not in SMT: " ++ show s ++ show (M.keys fs)

getTopLevelFunc s = do
    sn <- smtName $ topLevelPath s
    getFunc sn

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
lengthConstant s = 
    case s of
      "nonce" -> return $ SApp [SAtom "NameKindLength", SAtom "Nonce"]    
      "DH" -> return $ SApp [SAtom "NameKindLength", SAtom "DHkey"]
      "enckey" -> return $ SApp [SAtom "NameKindLength", SAtom "Enckey"]
      "pkekey" -> return $ SApp [SAtom "NameKindLength", SAtom "PKEkey"]
      "sigkey" -> return $ SApp [SAtom "NameKindLength", SAtom "Sigkey"]
      "prfkey" -> return $ SApp [SAtom "NameKindLength", SAtom "PRFkey"]
      "mackey" -> return $ SApp [SAtom "NameKindLength", SAtom "MACkey"]
      "signature" -> return $ SAtom "SignatureLen"
      "vk" -> return $ SAtom "VKLen"
      "maclen" -> return $ SAtom "MAClen"
      "tag" -> return $ SAtom "Taglen"


setupAllFuncs :: Sym ()
setupAllFuncs = do
    fncs <- view detFuncs
    mapM_ setupFunc $ map (\(k, (v, _)) -> (PDot PTop k, v)) fncs
    ufs <- liftCheck $ collectUserFuncs
    mapM_ setupUserFunc $ map (\(k, v) -> (pathPrefix k, v)) ufs 

sLambda :: (SExp -> SExp) -> SExp
sLambda k = 
    let x = SAtom "%x" in
    SApp [SAtom "lambda", SApp [SApp [x, SAtom "Bits"]], k x]

sRefined :: SExp -> (SExp -> SExp) -> SExp
sRefined v k = 
    SApp [SAtom "Refined", v, sLambda k]

smtTy :: Ty -> Sym SExp
smtTy t = 
    case t^.val of
      TData _ _ -> return $ SAtom "Data"
      TDataWithLength _ a -> do
          v <- interpretAExp a
          return $ sRefined (SAtom "Data") $ \x -> (sLength x) `sEq` v
      TBool _ -> return $ SAtom "TBool"  
      TRefined t xp -> do
          vt <- smtTy t
          (x, p) <- liftCheck $ unbind xp
          vE <- use varVals
          varVals %= (M.insert x (SAtom (show x)))
          v2 <- interpretProp p
          varVals .= vE
          return $ SApp [SAtom "Refined", vt, SApp [SAtom "lambda", SApp [SApp [SAtom (show x), SAtom "Bits"]], v2]]
      TOption t -> do
          vt <- smtTy t
          return $ sEnumType [SAtom "Unit", vt]
      TName n -> do
          liftCheck $ debug $ pretty "TName" <+> pretty n
          vn <- getSymName n
          return $ SApp [SAtom "TName", vn]
      TVK n -> do
          vn <- symNameExp n
          vk <- getTopLevelFunc ("vk")
          return $ sRefined (SAtom "Data") $ \x -> x `sEq` (SApp [vk, vn])
      TDH_PK n -> do
          vn <- symNameExp n
          dhpk <- getTopLevelFunc ("dhpk")
          return $ sRefined (SAtom "Data") $ \x -> x `sEq` (SApp [dhpk, vn])
      TEnc_PK n -> do
          vn <- symNameExp n
          encpk <- getTopLevelFunc ("enc_pk")
          return $ sRefined (SAtom "Data") $ \x -> x `sEq` (SApp [encpk, vn])
      TSS n m -> do
          vn <- symNameExp n
          vm <- symNameExp m
          dhpk <- getTopLevelFunc ("dhpk")
          dh_combine <- getTopLevelFunc ("dh_combine")
          return $ sRefined (SAtom "Data") $ \x -> x `sEq` (SApp [dh_combine, SApp [dhpk, vn], vm])
      TUnit -> return $ SAtom "Unit"
      TAdmit -> return $ SAtom "Unit"
      TUnion t1 t2 -> do
          vt1 <- smtTy t1
          vt2 <- smtTy t2
          return $ SApp [SAtom "Union", vt1, vt2]
      TCase p t1 t2 -> do
          vp <- interpretProp p
          vt1 <- smtTy t1
          vt2 <- smtTy t2
          return $ SApp [SAtom "TCase", vp, vt1, vt2]
      TExistsIdx _ -> return $ SAtom "Data" -- Opaque to SMT
      TConst s@(PRes (PDot pth _)) ps -> do
          td <- liftCheck $ getTyDef (t^.spanOf) s
          case td of
            TyAbstract -> return $ SAtom "Data"
            TyAbbrev t -> smtTy t
            StructDef ixs -> do
                dts <- liftCheck $ extractStruct (t^.spanOf) ps (show s) ixs
                vts <- forM dts $ \(_, t) -> smtTy t
                return $ sIterPair vts
            EnumDef ixs -> do
                dts <- liftCheck $ extractEnum (t^.spanOf) ps (show s) ixs
                vts <- forM dts $ \(_, ot) -> 
                    case ot of
                      Just t -> smtTy t
                      Nothing -> return $ SAtom "Unit"
                return $ sEnumType vts

            
sIterPair :: [SExp]  -> SExp
sIterPair [] = error "Got empty list in sIterPair"
sIterPair [x] = x
sIterPair (x:xs) = SApp [SAtom "Pair", x, sIterPair xs]

sTypeSeq :: [SExp] -> SExp
sTypeSeq [] = SAtom "(as seq.empty (Seq Type))"
sTypeSeq (x:xs) = SApp [SAtom "seq.++", SApp [SAtom "seq.unit", x], sTypeSeq xs]

sEnumType :: [SExp] -> SExp
sEnumType xs = SApp [SAtom "Enum", sTypeSeq xs]

tyConstraints :: Ty -> SExp -> Sym SExp
tyConstraints t v = do
    vt <- smtTy t
    return $ SApp [SAtom "HasType", v, vt]

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
          f | f `aeq` (topLevelPath "UNIT") -> return unit
          f | f `aeq` (topLevelPath "TRUE") -> return bTrue
          f | f `aeq` (topLevelPath "FALSE") -> return bFalse
          _ -> do
              vf <- getFunc =<< (smtName f)
              return $ sApp $ vf : vs
      AEString s -> return $ SApp [SAtom "S2B", SAtom $ "\"" ++ s ++ "\""]
      AELenConst s -> symLenConst s
      AEInt i -> return $ SApp [SAtom "I2B", SAtom (show i)]
      AEGet ne -> do
          liftCheck $ debug $ pretty "AEGet" <+> pretty ne
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
      (PEq p1 p2) -> do
          v1 <- interpretAExp p1
          v2 <- interpretAExp p2
          return $ SApp [SAtom "=", SAtom "TRUE", SApp [SAtom "eq", v1, v2]]
      (PRO p1 p2 i) -> do
          v1 <- interpretAExp p1
          v2 <- interpretAExp p2
          return $ SApp [SAtom "RO", v1, v2, SAtom $ show i]
      (PEqIdx i1 i2) ->
        liftM2 (sEq) (symIndex i1) (symIndex i2)
      (PIsConstant a) -> do
          v <- interpretAExp a
          return $ SApp [SAtom "IsConstant", v]
      (PQuantIdx q ip) -> do
          (i, p') <- liftCheck $ unbind ip
          sIE <- use symIndexEnv
          symIndexEnv  %= (M.insert i (SAtom $ show i))
          v <- local (over inScopeIndices $ TypingBase.insert i IdxGhost) $ interpretProp p'
          symIndexEnv .= sIE
          case q of
            Forall -> return $ sForall [(SAtom $ show i, indexSort)] v [] $ "forall_" ++ show i
            Exists -> return $ sExists [(SAtom $ show i, indexSort)] v [] $ "exists_" ++ show i
      (PHappened s (id1, id2) xs) -> do
          vs <- mapM interpretAExp xs
          ivs <- mapM symIndex id1
          ivs' <- mapM symIndex id2
          sn <- smtName s
          return $ SApp $ [SAtom "Happened", SAtom ("\"" ++ sn ++ "\""), mkSList "Index" (ivs ++ ivs'), mkSList "Bits" vs]
      (PFlow l1 l2 ) -> do
        x <- symLabel l1
        y <- symLabel l2
        return $ SApp [SAtom "Flows", x, y]
         
mkSList :: String -> [SExp] -> SExp
mkSList sort [] = SApp [SAtom "as", SAtom "nil", SAtom ("(List " ++ sort ++")")]
mkSList sort (x:xs) = SApp [SAtom "insert", x, mkSList sort xs]
    
subTypeCheck :: Ty -> Ty -> Sym ()
subTypeCheck t1 t2 = do
    v <- mkTy Nothing t1
    c <- tyConstraints t2 v
    emitComment $ "Checking subtype " ++ show (pretty t1) ++ " <= " ++ show (pretty t2)
    emitToProve c

sConcats :: [SExp] -> SExp
sConcats vs = 
    let sConcat a b = SApp [SAtom "concat", a, b] in
    foldl sConcat (head vs) (tail vs) 


symROUnique :: [Bind ([IdxVar], [IdxVar]) [AExpr]] -> [AExpr] -> Sym ()
symROUnique roPres e = do
    v <- sConcats <$> mapM interpretAExp e
    bs <- forM (zip roPres [0..(length roPres - 1)]) $ \(bnd, j) -> do
        ((is, ps), aes) <- liftCheck $ unbind bnd
        let ivs = map (\i -> SAtom (show i)) $ is ++ ps
        withIndices (map (\i -> (i, IdxGhost)) (is ++ ps)) $ do
            vs <- mapM interpretAExp aes
            return $ sForall
                (map (\i -> (i, indexSort)) ivs)
                (sNot $ sEq (SAtom "TRUE") $ SApp [SAtom "eq", sConcats vs, v])
                []
                ("ro_unique_" ++ show j)
    emitToProve $ sAnd bs

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

symDecideNotInRO :: [AExpr] -> Check Bool
symDecideNotInRO aes = do
    debug $ pretty "symDecideNotInRO" <+> pretty aes
    if length aes == 0 then return True else do
        res <- fromSMT smtSetup $ do
            vs <- mapM interpretAExp aes
            roPres <- liftCheck $ collectROPreimages
            bs <- forM (zip roPres [0 .. (length roPres - 1)]) $ \(b, j) -> do 
                ((is, ps), aes') <- liftCheck $ unbind b
                let ivs = map (\i -> SAtom (show i)) $ is ++ ps
                withIndices (map (\i -> (i, IdxGhost)) (is ++ ps)) $ do
                    vs' <- mapM interpretAExp aes'
                    return $ sForall
                        (map (\i -> (i, indexSort)) ivs)
                        (sNot $ sEq (sConcats vs) (sConcats vs'))
                        []
                        ("not_in_ro_" ++ show j)
            emitToProve $ sAnd bs
        if snd res then return True else return False


symDecideProp :: Prop -> Check (Maybe String, Maybe Bool) 
symDecideProp p = do
    let k1 = do {
        emitComment $ "Trying to prove prop " ++ show (pretty p);
        b <- interpretProp p;
        emitToProve b 
                }
    let k2 = do {
        emitComment $ "Trying to prove prop " ++ show (pretty $ pNot p);
        b <- interpretProp $ pNot p;
        emitToProve b 
                }
    raceSMT smtSetup k2 k1

checkFlows :: Label -> Label -> Check (Maybe String, Maybe Bool)
checkFlows l1 l2 = do
    let k1 = do {
        emitComment $ "Trying to prove " ++ show (pretty l1) ++ " <= " ++ show (pretty l2);
        x <- symLabel l1;
        y <- symLabel l2;
        emitToProve $ SApp [SAtom "Flows", x, y]
                }
    let k2 = do {
        emitComment $ "Trying to prove " ++ show (pretty l1) ++ " !<= " ++ show (pretty l2);
        x <- symLabel l1;
        y <- symLabel l2;
        emitToProve $ sNot $ SApp [SAtom "Flows", x, y]
                }
    raceSMT smtSetup k2 k1

