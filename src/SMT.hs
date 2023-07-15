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
            setupAllFuncs 
            liftCheck $ debug $ pretty $ "Index env"
            setupIndexEnv
            liftCheck $ debug $ pretty $ "Setup name env and RO"
            setupNameEnvRO
            liftCheck $ debug $ pretty $ "Label setup"
            smtLabelSetup 
            liftCheck $ debug $ pretty $ "Setup ty env"
            setupTyEnv 
            liftCheck $ debug $ pretty $ "Func axioms"
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

addSymName :: String -> SExp -> Sym ()
addSymName s e = do
    liftCheck $ debug $ pretty $ "Adding sym name " ++ s
    symNameEnv %= M.insert s e


setupNameEnvRO :: Sym ()
setupNameEnvRO = do
    nE <- liftCheck $ collectNameEnv
    forM_ nE $ \(n, o) -> do
        ((is1, is2), ntLclsOpt) <- liftCheck $ unbind o
        sn <- smtName n
        let sname = SAtom $ "%name_" ++ sn
        addSymName sn sname
        let ar = length is1 + length is2
        emit $ SApp [SAtom "declare-fun", sname, SApp (replicate ar (indexSort)), nameSort]
    liftCheck $ debug $ pretty "Adding name kind axioms"
    forM_ nE $ \(n, o) -> do 
        ((is1, is2), ntLclsOpt) <- liftCheck $ unbind o
        let ntOpt = case ntLclsOpt of
                    Nothing -> Nothing -- liftCheck $ typeError $ ErrNameStillAbstract n
                    Just (nt', _) -> Just nt'
        let ar = length is1 + length is2
        sn <- smtName n
        let sname = SAtom $ "%name_" ++ sn
        case ntOpt of 
          Nothing -> return ()
          Just nt -> do
            let is = is1 ++ is2
            let ivs = map (\i -> SAtom (show i)) is
            nk <- nameKindOf nt
            emitAssertion $ sForall
                (map (\i -> (i, indexSort)) ivs)
                (SApp [SAtom "HasNameKind", sBaseName sname ivs, nk])
                [sBaseName sname ivs]
            sIE <- use symIndexEnv
            symIndexEnv  %= (M.union $ M.fromList $ map (\i -> (i, SAtom $ show i)) is1)
            symIndexEnv  %= (M.union $ M.fromList $ map (\i -> (i, SAtom $ show i)) is2)
            liftCheck $ debug $ pretty "Adding name def flows"
            local (over (inScopeIndices) $ (++) $ map (\i -> (i, IdxSession)) is1) $ 
                local (over (inScopeIndices)  $ (++) $ map (\i -> (i, IdxPId)) is2) $ do
                    let nexp = mkSpanned $ BaseName (map (IVar (ignore def)) is1, map (IVar (ignore def)) is2) (PRes n)
                    emitComment $ "nameDefFlows for" ++ show (pretty nexp)                                
                    lAxs <- nameDefFlows nexp nt
                    sAxs <- forM lAxs $ \(l1, l2) -> do
                        vl1 <- symLabel l1
                        vl2 <- symLabel l2
                        return $ SApp [SAtom "Flows", vl1, vl2]
                    emitAssertion $ sForall
                        (map (\i -> (i, indexSort)) ivs)
                        (sAnd sAxs)
                        [sBaseName sname ivs] 
            symIndexEnv .= sIE

    -- Disjointness across names
    emitComment $ "Disjointness across names"
    when (not $ null nE) $ do
           let different_pairs = [(x, y) | (x : ys) <- tails nE, y <- ys]
           forM_ different_pairs $ \((n1, o1), (n2, o2)) -> do
               ((is1, is2), _) <- liftCheck $ unbind o1
               ((is1', is2'), _) <- liftCheck $ unbind o2
               let ar1 = length is1 + length is2
               let ar2 = length is1' + length is2'
               sn1 <- smtName n1
               sn2 <- smtName n2
               emitComment $ "Disjointness " ++ sn1 ++ " <-> " ++ sn2
               ivs1' <- forM [1..ar1] $ \_ -> freshSMTIndexName
               ivs2' <- forM [1..ar2] $ \_ -> freshSMTIndexName
               let ivs1 = map SAtom ivs1'
               let ivs2 = map SAtom ivs2'
               let v1 = sBaseName (SAtom $ "%name_" ++ sn1) (take ar1 ivs1)
               let v2 = sBaseName (SAtom $ "%name_" ++ sn2) (take ar2 ivs2)
               emitAssertion $ sForall (map (\i -> (i, indexSort)) (ivs1 ++ ivs2)) (sNot $ sEq v1 v2) [v1, v2]
    ros <- liftCheck $ collectRO
    forM_ ros $ \(s, bnd) -> do
        (is, (ae, nts)) <- liftCheck $ unbind bnd
        sn <- smtName s
        let sname = SAtom $ "%ro_" ++ sn
        addSymName sn sname
        let ar = length is
        emit $ SApp [SAtom "declare-fun", sname, SApp (replicate ar (indexSort) ++ [SAtom "Int"]), nameSort]
    forM_ ros $ \(s, bnd) -> do
        sn <- smtName s
        let sname = SAtom $ "%ro_" ++ sn
        (is, (ae, nts)) <- liftCheck $ unbind bnd
        let ivs = map (\i -> SAtom (show i)) is
        emitComment $ "nameDefFlows for RO " ++ sn ++ " : " ++ show (length ivs)
        sIE <- use symIndexEnv
        symIndexEnv  %= (M.union $ M.fromList $ map (\i -> (i, SAtom $ show i)) is)
        local (over inScopeIndices $ (++) $ map (\i -> (i, IdxGhost)) is) $ do 
            forM_ [0 .. (length nts - 1)] $ \i -> do
                lAxs <- nameDefFlows (roName (PRes s) (map (IVar (ignore def)) is) i) (nts !! i)
                sAxs <- forM lAxs $ \(l1, l2) -> do
                    vl1 <- symLabel l1
                    vl2 <- symLabel l2
                    return $ SApp [SAtom "Flows", vl1, vl2]
                emitAssertion $ sForall
                    (map (\i -> (i, indexSort)) ivs)
                    (sAnd sAxs)
                    [sROName sname ivs i]
        symIndexEnv .= sIE

nameKindOf :: NameType -> Sym SExp
nameKindOf nt = 
    return $ case nt^.val of
      NT_DH -> SAtom "DHkey"
      NT_Enc _ -> SAtom "Enckey"
      NT_EncWithNonce _ _ _ -> SAtom "Enckey"
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
      TBool _ -> return $ SAtom "Bool"  
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
              return $ sApp vf vs
      AEString s -> return $ SApp [SAtom "S2B", SAtom $ "\"" ++ s ++ "\""]
      AELenConst s -> symLenConst s
      AEInt i -> return $ SApp [SAtom "I2B", SAtom (show i)]
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
      (PEq p1 p2) -> do
          v1 <- interpretAExp p1
          v2 <- interpretAExp p2
          return $ SApp [SAtom "=", SAtom "TRUE", SApp [SAtom "eq", v1, v2]]
      (PEqIdx i1 i2) ->
        liftM2 (sEq) (symIndex i1) (symIndex i2)
      (PHappened s (id1, id2) xs) -> do
          vs <- mapM interpretAExp xs
          ivs <- mapM symIndex id1
          ivs' <- mapM symIndex id2
          sn <- smtName s
          return $ SApp $ [SAtom "Happened", SAtom ("\"" ++ sn ++ "\""), mkSList "Index" (ivs ++ ivs'), mkSList "Bits" vs]
      (PFlow l1 l2 ) -> do
        liftCheck $ debug $ pretty "Interpreting prop " <> pretty l1 <+> pretty "<=" <+> pretty l2
        x <- symLabel l1
        y <- symLabel l2
        return $ SApp [SAtom "Flows", x, y]
         
mkSList :: String -> [SExp] -> SExp
mkSList sort [] = SApp [SAtom "as", SAtom "nil", SAtom ("(List " ++ sort ++")")]
mkSList sort (x:xs) = SApp [SAtom "insert", x, mkSList sort xs]

emitFuncAxioms :: Sym () 
emitFuncAxioms = do
    emitComment $ "RO equality axioms"
    ros <- liftCheck $ collectRO
    let sConcat a b = SApp [SAtom "concat", a, b]
    forM_ ros $ \(s, bnd) -> do 
        (is, (aes, nts)) <- liftCheck $ unbind bnd
        let ivs = map (\i -> SAtom (show i)) is
        sIE <- use symIndexEnv
        symIndexEnv  %= (M.union $ M.fromList $ map (\i -> (i, SAtom $ show i)) is)
        local (over inScopeIndices $ (++) $ map (\i -> (i, IdxGhost)) is) $ do  
            vs <- mapM interpretAExp aes
            let v = foldr sConcat (head vs) (tail vs) 
            sn <- smtName s
            let sname = SAtom $ "%ro_" ++ sn
            forM_ [0 .. (length nts - 1)] $ \i -> do
                emitAssertion $ 
                    sForall 
                        (map (\i -> (i, indexSort)) ivs)
                        (sEq (sValue $ sROName sname ivs i) (sHashSelect v i))
                        [sValue $ sROName sname ivs i]
        symIndexEnv .= sIE
    
subTypeCheck :: Ty -> Ty -> Sym ()
subTypeCheck t1 t2 = do
    liftCheck $ debug $ pretty "Checking subtype " <> pretty t1 <+> pretty "<=" <+> pretty t2
    v <- mkTy Nothing t1
    c <- tyConstraints t2 v
    emitComment $ "Checking subtype " ++ show (pretty t1) ++ " <= " ++ show (pretty t2)
    emitToProve c

sConcats :: [SExp] -> SExp
sConcats vs = 
    let sConcat a b = SApp [SAtom "concat", a, b] in
    foldr sConcat (head vs) (tail vs) 





symROUnique :: (Map String (Bind [IdxVar] ([AExpr], [NameType]))) -> [AExpr] -> Sym ()
symROUnique ro e = do
    v <- sConcats <$> mapM interpretAExp e
    bs <- forM ro $ \(_, bnd) -> do
        (is, (aes, _)) <- liftCheck $ unbind bnd
        let ivs = map (\i -> SAtom (show i)) is
        sIE <- use symIndexEnv
        symIndexEnv  %= (M.union $ M.fromList $ map (\i -> (i, SAtom $ show i)) is)
        b <- local (over inScopeIndices $ (++) $ map (\i -> (i, IdxGhost)) is) $ do  
            vs <- mapM interpretAExp aes
            return $ sForall
                (map (\i -> (i, indexSort)) ivs)
                (sNot $ sEq (SAtom "TRUE") $ SApp [SAtom "eq", sConcats vs, v])
                []
        symIndexEnv .= sIE
        return b
    emitToProve $ sAnd bs

symListUniq :: [AExpr] -> Sym ()
symListUniq es = do
    liftCheck $ debug $ pretty "symListUniq with " <+> pretty es
    vs <- mapM interpretAExp es
    emitComment $ "Proving symListUniq with es = " ++ show (pretty es)
    emitToProve $ sDistinct vs
    return ()

---- First AExpr is in the top level (ie, only names), second is regular
symCheckEqTopLevel :: [AExpr] -> [AExpr] -> Sym ()
symCheckEqTopLevel eghosts es = do
    liftCheck $ debug $ pretty "symCheckEqTopLevel for " <> pretty eghosts <+> pretty " and " <+> pretty es
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
    liftCheck $ debug $ pretty "symAssert for " <> pretty p
    b <- interpretProp p
    emitComment $ "Proving prop " ++ show (pretty p)
    emitToProve b

symDecideNotInRO :: [AExpr] -> Check Bool
symDecideNotInRO aes = do
    debug $ pretty "symDecideNotInRO for " <> pretty aes
    if length aes == 0 then return True else do
        res <- fromSMT smtSetup $ do
            vs <- mapM interpretAExp aes
            ros <- liftCheck $ collectRO
            bs <- forM ros $ \(_, bs) -> do 
                (is, (aes', _)) <- unbind bs 
                let ivs = map (\i -> SAtom (show i)) is
                sIE <- use symIndexEnv
                symIndexEnv  %= (M.union $ M.fromList $ map (\i -> (i, SAtom $ show i)) is)
                b <- local (over inScopeIndices $ (++) $ map (\i -> (i, IdxGhost)) is) $ do  
                    vs' <- mapM interpretAExp aes'
                    return $ sForall
                        (map (\i -> (i, indexSort)) ivs)
                        (sNot $ sEq (sConcats vs) (sConcats vs'))
                        []
                symIndexEnv .= sIE
                return b
            emitToProve $ sAnd bs
        if snd res then return True else return False


symDecideProp :: Prop -> Check (Maybe String, Maybe Bool) 
symDecideProp p = do
    debug $ pretty "symDecideProp for " <> pretty p
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
    debug $ pretty "checkFlows for " <> pretty l1 <+> pretty "and" <+> pretty l2
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

