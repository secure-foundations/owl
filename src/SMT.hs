{-# LANGUAGE TemplateHaskell #-} 
{-# LANGUAGE MultiParamTypeClasses #-} 
{-# LANGUAGE GeneralizedNewtypeDeriving #-} 
{-# LANGUAGE ScopedTypeVariables #-} 
{-# LANGUAGE TypeSynonymInstances #-} 
{-# LANGUAGE FlexibleInstances #-} 
module SMT where
import AST
import Data.List
import Control.Monad
import Numeric (readHex)
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
import Pretty
import SMTBase
import Data.IORef
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

-- The module-level setup does not depend on the current type context and is by far
-- the most expensive piece to produce (name disjointness alone is quadratic
-- in the number of names), so it is shared across queries. The context setup
-- is incremental: every new binder extends from its nearest ancestor's solver setup.
smtSetup :: Sym ()
smtSetup = do
    p_solverEnv <- view $ curMemo . memoSolverEnv
    key <- liftCheck moduleFingerprint
    smtenv <- liftIO $ readIORef p_solverEnv
    case smtenv of
      Just senv | senv ^. smtGlobalKey == key -> put senv
      _ -> do
            stack <- view memoStack
            ancestors <- liftIO $ mapM (readIORef . _memoSolverEnv) (drop 1 stack)
            case [senv | Just senv <- ancestors, senv ^. smtGlobalKey == key] of
              (senv : _) -> put senv
              [] -> globalSMTSetup key
            setupIndexEnvIncremental
            setupTyEnvIncremental
            ctxLog <- use smtLog
            smtLog .= []
            let ctxText = renderSMTLog ctxLog
            smtContextText %= (\t -> if T.null t then ctxText else t <> T.pack "\n" <> ctxText)
            senv <- get
            liftIO $ writeIORef p_solverEnv $ Just senv

-- Initialize a solver env with an empty log and type context. Keep fresh-name counter
-- so that later context setup does not clash with the names declared here.
globalSMTSetup :: ModuleFingerprint -> Sym ()
globalSMTSetup key = do
    ref <- view globalSMTSetupCache
    cached <- liftIO $ readIORef ref
    case cached of
      Just (k, senv) | k == key -> put senv
      _ -> do
            put initSolverEnv
            emitComment $ T.pack $ "SMT SETUP: module-level declarations and axioms"
            setupAllFuncs
            declareKDFRules
            setupNameEnvRO
            setupKDFRules
            smtLabelSetup
            log <- use smtLog
            prelude <- liftIO $ T.readFile "prelude.smt2"
            smtLog .= []
            smtPreludeText .= prelude
            smtGlobalText .= renderSMTLog log
            smtGlobalKey .= key
            senv <- get
            liftIO $ writeIORef ref $ Just (key, senv)

smtTypingQuery s = fromSMT initSolverEnv s smtSetup

-- Append index env to the solver state, oldest first.
setupIndexEnvIncremental :: Sym ()
setupIndexEnvIncremental = do
    inds <- view $ inScopeIndices
    known <- use symIndexEnv
    let new = filter (\i -> not (M.member i known)) (map fst inds)
    forM_ (reverse new) $ \i -> do
        x <- freshIndexVal (cleanSMTIdent $ show i)
        symIndexEnv %= M.insert i x

sZero :: SExp
sZero = SAtom "zero"


setupNameEnvRO :: Sym ()
setupNameEnvRO = do
    dfs <- liftCheck $ collectNameDefs
    fdfs <- flattenNameDefs dfs
    forM_ fdfs $ \fd -> do
        case fd of
          SMTBaseName (sn, _) bnd -> do
              let ((is, ps), _) = unsafeUnbind bnd
              let iar = length is + length ps
              emit $ SApp [SAtom "declare-fun", sn, SApp (replicate iar indexSort), nameSort]
          --SMTROName (sn, _) _ bnd -> do
          --    let (((is, ps), xs), _) = unsafeUnbind bnd
          --    let iar = length is + length ps
          --    let var = length xs
          --    emit $ SApp [SAtom "declare-fun", sn, SApp (replicate iar indexSort ++ replicate var bitstringSort), nameSort]
    mkCrossDisjointness fdfs
    mkSelfDisjointness fdfs
    -- Axioms relevant for each def 
    forM_ fdfs $ \fd -> do
        withSMTNameDef fd $ \(sn, pth) ((is, ps)) ont -> do
            -- Name def flows
            case ont of
              Nothing -> return ()
              Just nt -> do
                let ivs = map (\i -> (SAtom (show i), indexSort)) (is ++ ps)
                withSMTIndices (map (\i -> (i, IdxSession)) is ++ map (\i -> (i, IdxPId)) ps) $ do
                    -- withSMTVars xs $ do 
                        nk <- liftCheck $ smtNameKindOf nt
                        emitAssertion $ sForall
                            (ivs)
                            (SApp [SAtom "HasNameKind", sApp (sn : (map fst ivs)), nk])
                            [sApp (sn : (map fst ivs))] --  ++ (map fst xvs))]
                            ("nameKind_" ++ (T.unpack $ renderSExp sn))

                        let nameExp = mkSpanned $ NameConst (map (\x -> IVar (ignore def) (ignore $ show x) x) is, map (\x -> IVar (ignore def) (ignore $ show x) x) ps) (PRes pth) [] 

                        -- No applicable KDF rule instance derives the value of a base name
                        scopes <- kdfScopeTags
                        forM_ scopes $ \tag -> 
                            emitAssertion $ sForall ivs
                                (sEq (SApp [SAtom tag, sValue $ sApp (sn : (map fst ivs))]) (SAtom "0"))
                                [sApp (sn : (map fst ivs))]
                                ("kdfTag_" ++ (T.unpack $ renderSExp sn))

                        -- A base name is not a KEM shared secret
                        emitAssertion $ sForall ivs
                            (sNot $ SApp [SAtom "NameIsKEM", sApp (sn : (map fst ivs))])
                            [sApp (sn : (map fst ivs))]
                            ("notKEM_" ++ (T.unpack $ renderSExp sn))

                        lAxs <- nameDefFlows nameExp nt
                        emitAssertion $ sForall (ivs)
                            lAxs
                            [sApp (sn : (map fst ivs))]
                            ("nameDefFlows_" ++ (T.unpack $ renderSExp sn))
            -- Solvability
            --case oi of
            --  Nothing -> return () -- Not RO
            --  Just i -> do 
            --    when (length xs == 0) $ do
            --        withIndices (map (\i -> (i, IdxSession)) is ++ map (\i -> (i, IdxPId)) ps) $ do
            --            let nameExp = mkSpanned $ NameConst (map (IVar (ignore def)) is, map (IVar (ignore def)) ps) (PRes pth) (Just ([], i)) 
            --            preimage <- liftCheck $ getROPreimage (PRes pth) (map (IVar (ignore def)) is, map (IVar (ignore def)) ps) []
            --            solvability <- liftCheck $ solvabilityAxioms preimage nameExp
            --            vsolv <- interpretProp solvability
            --            let ivs = map (\i -> (SAtom (show i), indexSort)) (is ++ ps)
            --            emitAssertion $ sForall ivs vsolv [sApp (sn : map fst ivs)] ("solvability_" ++ show sn)  

-- %kdftag_S is a trick for stating "different rules never produce the same
-- value" with one axiom per rule, instead of one axiom per pair of rules.
-- For each kdf_scope S, %kdftag_S(v) is the identifier of the rule of S that
-- has an applicable instance with value v, and 0 if there is none. That this
-- is well defined is what the disjointness checks on the rules of S establish.
kdfScopeTag :: ResolvedPath -> KDFRuleDef -> Sym String
kdfScopeTag pth rd = do
    s <- smtName $ PRes $ PDot (pathPrefix pth) (_kdfRuleScope rd)
    return $ "%kdftag_" ++ s

kdfScopeTags :: Sym [String]
kdfScopeTags = do
    rules <- liftCheck collectKDFRules
    nub <$> mapM (uncurry kdfScopeTag) rules

-- The theory of KDF-derived names (docs/kdf-scopes.md, section 6). Output j of
-- the instance of rule L with parameters p is the name %kdf_L(p, j); the
-- instance is applicable (where clause and a secret input) when %app_L(p).
declareKDFRules :: Sym ()
declareKDFRules = do
    rules <- liftCheck collectKDFRules
    tags <- kdfScopeTags
    forM_ tags $ \tag -> emit $ SApp [SAtom "declare-fun", SAtom tag, SApp [bitstringSort], SAtom "Int"]
    forM_ rules $ \(pth, rd) -> do
        sl <- smtName (PRes pth)
        let (((is, ps), xs), _) = unsafeUnbind $ _kdfRuleBody rd
        let sorts = replicate (length is + length ps) indexSort ++ replicate (length xs) bitstringSort
        emit $ SApp [SAtom "declare-fun", SAtom ("%kdf_" ++ sl), SApp (sorts ++ [SAtom "Int"]), nameSort]
        emit $ SApp [SAtom "declare-fun", SAtom ("%app_" ++ sl), SApp sorts, SAtom "Bool"]

setupKDFRules :: Sym ()
setupKDFRules = do
    rules <- liftCheck collectKDFRules
    -- A rule has no theory until it has passed its declaration-time checks
    forM_ (zip [1 :: Int ..] rules) $ \(ruleId, (pth, rd)) -> when (_kdfRuleChecked rd) $ do
        sl <- smtName (PRes pth)
        let sApp' ps = sApp $ SAtom ("%app_" ++ sl) : ps
        let idxVar i = SAtom $ cleanSMTIdent $ show i
        let dataVar x = SAtom $ cleanSMTIdent $ show x
        (((is, ps), xs), rule) <- liftCheck $ unbind $ _kdfRuleBody rd
        let outs = _kdfOutputs rule
        -- Facts about all instances of the rule
        nks <- withSMTIndices (map (\i -> (i, IdxGhost)) (is ++ ps)) $ withSMTVars xs $ do
            nks <- liftCheck $ mapM (getNameKind . snd) outs
            let qvars = map (\i -> (idxVar i, indexSort)) (is ++ ps) ++ map (\x -> (dataVar x, bitstringSort)) xs
            let params = map fst qvars
            let ax nm body j = emitAssertion $ sForall qvars body [sKDFName sl params (SAtom $ show j)] (nm ++ "_" ++ sl ++ "_" ++ show j)
            vwhere <- interpretProp $ _kdfWhere rule
            forM_ (zip [0 :: Int ..] outs) $ \(j, (strictness, nt)) -> do
                let ne = mkSpanned $ KDFName (KDFRuleRef (PRes pth) (map mkIVar is, map mkIVar ps) (map aeVar' xs)) nks j
                let nm = sKDFName sl params (SAtom $ show j)
                nk <- liftCheck $ smtNameKindOf nt
                ax "kdf_kind" (SApp [SAtom "HasNameKind", nm, nk]) j
                ax "kdf_not_kem" (sNot $ SApp [SAtom "NameIsKEM", nm]) j
                -- Only an applicable instance is secret
                vcorr <- symLabel (nameLbl ne) >>= \l -> sFlows l <$> symLabel advLbl
                ax "kdf_label" (case strictness of
                                  KDFPub -> vcorr
                                  _ -> sImpl (sNot $ sApp' params) vcorr) j
                flows <- nameDefFlows ne nt
                ax "kdf_flows" (sImpl vwhere flows) j
                -- The value of an applicable instance is not equal to the value of any other instance,
                -- or of any other base name
                tagFn <- kdfScopeTag pth rd
                let tag = SApp [SAtom tagFn, sValue nm]
                ax "kdf_tag" (sAnd2 (sImpl (sApp' params) (sEq tag (SAtom $ show ruleId)))
                                    (sOr (sEq tag (SAtom $ show ruleId)) (sEq tag (SAtom "0")))) j
            -- Two instances, one of them applicable, with the same value are the same instance
            let qvars2 = map (\(v, srt) -> (SAtom $ T.unpack (renderSExp v) ++ "_2", srt)) qvars
            let (j1, j2) = (SAtom "%j1", SAtom "%j2")
            let (nm1, nm2) = (sKDFName sl params j1, sKDFName sl (map fst qvars2) j2)
            emitAssertion $ sForall (qvars ++ qvars2 ++ [(j1, SAtom "Int"), (j2, SAtom "Int")])
                (sImpl (sAnd2 (sOr (sApp' params) (sApp' $ map fst qvars2))
                              (sEq (SAtom "TRUE") (SApp [SAtom "eq", sValue nm1, sValue nm2])))
                       (sAnd $ sEq j1 j2 : zipWith sEq params (map fst qvars2)))
                [nm1, nm2]
                ("kdf_self_disj_" ++ sl)
            return nks
        -- Facts about each case of the rule
        insts <- liftCheck $ kdfInsts (PRes pth)
        forM_ (zip [0 :: Int ..] insts) $ \(c, binst) -> do
            ((vs, xs'), inst) <- liftCheck $ unbind binst
            withSMTIndices (map (\i -> (i, IdxGhost)) vs) $ withSMTVars xs' $ do
                let qvars = map (\i -> (idxVar i, indexSort)) vs ++ map (\x -> (dataVar x, bitstringSort)) xs'
                let KDFRuleRef _ (ris, rps) ras = _kiRef inst
                params <- liftM2 (++) (mapM symIndex (ris ++ rps)) (mapM interpretAExp ras)
                vwhere <- interpretProp $ _kiWhere inst
                vapp <- interpretProp $ _kiApp inst
                emitAssertion $ sForall qvars (sEq (sApp' params) (sAnd2 vwhere vapp)) [sApp' params] 
                    ("kdf_app_" ++ sl ++ "_" ++ show c)
                let (salt, ikm, info) = _kiCase inst
                forM_ [0 .. length outs - 1] $ \j -> do
                    let nm = sKDFName sl params (SAtom $ show j)
                    v <- interpretAExp $ mkSpanned $ AEKDF salt ikm info nks j
                    emitAssertion $ sForall qvars (sImpl vwhere (sEq (sValue nm) v)) [nm]
                        ("kdf_valueof_" ++ sl ++ "_" ++ show c ++ "_" ++ show j)

mkCrossDisjointness :: [SMTNameDef] -> Sym ()
mkCrossDisjointness fdfs = do
    -- Get all pairs of fdfs
    let pairs = [(x, y) | (x : ys) <- tails fdfs, y <- ys]
    forM_ pairs $ \(fd1, fd2) -> 
        withSMTNameDef fd1 $ \(sn1, pth1) ((is1, ps1)) _ ->  
            withSMTNameDef fd2 $ \(sn2, pth2) ((is2, ps2)) _ ->  do
                let q1 = map (\i -> (SAtom $ show i, indexSort)) (is1 ++ ps1) 
                let q2 = map (\i -> (SAtom $ show i, indexSort)) (is2 ++ ps2) 
                let v1 = sApp (sn1 : (map fst q1))
                let v2 = sApp (sn2 : (map fst q2))
                let v1_eq_v2 = SApp [SAtom "=", SAtom "TRUE", SApp [SAtom "eq", SApp [SAtom "ValueOf", v1], 
                                                                             SApp [SAtom "ValueOf", v2]]]
                let pat = (if length q1 > 0 then [v1] else []) ++ (if length q2 > 0 then [v2] else [])
                emitAssertion $ sForall (q1 ++ q2) (sNot $ v1_eq_v2) pat $ "disj_" ++ T.unpack (renderSExp sn1) ++ "_" ++ T.unpack (renderSExp sn2) 
                --when (oi1 == Just 0 && oi2 == Just 0 && (not $ pth1 `aeq` pth2)) $ do 
                --    (vpre1, vprereq1) <- withIndices (map (\i -> (i, IdxSession)) is1 ++ map (\i -> (i, IdxPId)) ps1) $ do
                --        withSMTVars xs1 $ do 
                --            pi <- liftCheck $ getROPreimage (PRes pth1) (map (IVar (ignore def)) is1, map (IVar (ignore def)) ps1) (map aeVar' xs1) 
                --            vpi <- interpretAExp pi
                --            pr <- liftCheck $ getROPrereq (PRes pth1) (map (IVar (ignore def)) is1, map (IVar (ignore def)) ps1) (map aeVar' xs1) 
                --            vpr <- interpretProp pr
                --            return (vpi, vpr)
                --    (vpre2, vprereq2) <- withIndices (map (\i -> (i, IdxSession)) is2 ++ map (\i -> (i, IdxPId)) ps2) $ do
                --        withSMTVars xs2 $ do 
                --            pi <- liftCheck $ getROPreimage (PRes pth2) (map (IVar (ignore def)) is2, map (IVar (ignore def)) ps2) (map aeVar' xs2) 
                --            vpi <- interpretAExp pi
                --            pr <- liftCheck $ getROPrereq (PRes pth2) (map (IVar (ignore def)) is2, map (IVar (ignore def)) ps2) (map aeVar' xs2) 
                --            vpr <- interpretProp pr
                --            return (vpi, vpr)
                --    let vpre1_eq_v2 = SApp [SAtom "=", SAtom "TRUE", SApp [SAtom "eq", vpre1, vpre2]]
                --    emitComment $ "Preimage disjointness for " ++ show sn1 ++ " and " ++ show sn2
                --    emitAssertion $ sForall (q1 ++ q2) (sImpl (sAnd2 vprereq1 vprereq2) $ sNot $ vpre1_eq_v2) [vpre1_eq_v2] $ "disj_pre_" ++ show (sn1) ++ "_" ++ show (sn2) 


mkSelfDisjointness :: [SMTNameDef] -> Sym ()
mkSelfDisjointness fdfs = do
    -- TODO: factor in preqreqs?
    forM_ fdfs $ \fd -> 
        withSMTNameDef fd $ \(sn, pth) ((is1, ps1)) _ ->  do
            withSMTNameDef fd $ \_ ((is2, ps2)) _ -> do
                when ((length is1 + length ps1) > 0) $ do
                    let q1 = map (\i -> (SAtom $ show i, indexSort)) (is1 ++ ps1) -- ++ map (\x -> (SAtom $ show x, bitstringSort)) xs1
                    let q2 = map (\i -> (SAtom $ show i, indexSort)) (is2 ++ ps2) -- ++ map (\x -> (SAtom $ show x, bitstringSort)) xs2
                    let v1 = sApp (sn : (map fst q1))
                    let v2 = sApp (sn : (map fst q2))
                    let q1_eq_q2 = sAnd $ map (\i -> sEq (fst $ q1 !! i) (fst $ q2 !! i)) [0 .. (length q1 - 1)]
                    let v1_eq_v2 = SApp [SAtom "=", SAtom "TRUE", SApp [SAtom "eq", SApp [SAtom "ValueOf", v1], 
                                                                             SApp [SAtom "ValueOf", v2]]]
                    emitAssertion $ sForall (q1 ++ q2)
                        (v1_eq_v2 `sImpl` q1_eq_q2)
                        [v1, v2]
                        ("self_disj_" ++ T.unpack (renderSExp sn))








mkTy :: Maybe String -> Ty -> Sym SExp
mkTy s t = do
    x <- freshSMTVal (case s of
                     Nothing -> Nothing
                     Just x -> Just $ x ++ " : " ++ show (owlpretty t)
                  )
    c <- tyConstraints t x
    emitComment $ T.pack "ty constraint for " <> (renderSExp x) <> T.pack ": " <> optext t
    emitAssertion c
    return x

-- Append type context to the solver state, oldest first.
setupTyEnvIncremental :: Sym ()
setupTyEnvIncremental = do
    vE <- view tyContext
    go vE
    where
        go [] = return ()
        go ((x, (_, _, t)) : xs) = do
            known <- use varVals
            when (not (M.member x known)) $ do
                v <- mkTy (Just $ show x) t
                varVals %= (M.insert x v)
            go xs

depBindLength :: Alpha a => DepBind a -> Int
depBindLength (DPDone _) = 0
depBindLength (DPVar _ _ b) = 
    let (_, k) = unsafeUnbind b in
    1 + depBindLength k

-- TODO: reinterpret in terms of their SMT semantics
setupUserFunc :: (ResolvedPath, UserFunc) -> Sym ()
setupUserFunc (s, f) =
    case f of
      FunDef _ -> return ()
      StructConstructor tv -> do
        -- Concats
        td <- liftCheck $ getTyDef  (PRes $ PDot s tv)
        case td of
          StructDef idf -> do
              let ar = depBindLength $ snd $ unsafeUnbind idf 
              setupFunc (PDot s tv, ar)
          _ -> error $ "Struct not found: " ++ show tv
      StructProjector _ proj -> setupFunc (PDot s proj, 1) -- Maybe leave uninterpreted?
      EnumConstructor tv variant ->  do
        -- Concat the pair using EnumTag
        td <- liftCheck $ getTyDef (PRes $ PDot s tv)
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
          td <- liftCheck $ getTyDef (PRes $ PDot s tv)
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
builtInSMTFuncs = ["length", "eq", "plus", "mult", "UNIT", "true", "false", "andb", "concat", "zero", "dh_combine", "dhpk", "is_group_elem", "kem_pk", "crh", "xor", "Some?", "None?"]


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


constant :: String -> Sym SExp
constant s = do
    cs <- use constants
    case M.lookup s cs of
      Just v -> return v
      Nothing -> do 
          x <- freshSMTVal $ Just s
          constants %= (M.insert s x)
          return x



setupAllFuncs :: Sym ()
setupAllFuncs = do
    fncs <- view detFuncs
    mapM_ setupFunc $ map (\(k, (v, _)) -> (PDot PTop k, v)) fncs
    ufs <- liftCheck $ collectUserFuncs
    mapM_ setupUserFunc $ map (\(k, v) -> (pathPrefix k, v)) ufs 

smtTy :: SExp -> Ty -> Sym SExp
smtTy xv t = 
    case t^.val of
      TData _ _ _ -> return sTrue
      TGhost -> return sTrue
      TDataWithLength _ a -> do
          v <- interpretAExp a
          return $ sLength xv `sEq` v
      TBool _ -> return $ xv `sHasType` (SAtom "TBool")
      TRefined t s xp -> do
          vt <- smtTy xv t
          (x, p) <- liftCheck $ unbind xp
          vE <- use varVals
          varVals %= (M.insert x xv)
          v2 <- interpretProp p
          varVals .= vE
          return $ vt `sAnd2` v2
      TOption t -> sMkEnumCond xv [tUnit, t]
      TName n -> do
          vn <- getSymName n
          return $ xv `sHasType` (SApp [SAtom "TName", vn])
      TVK n -> do
          vn <- symNameExp n
          vk <- getTopLevelFunc ("vk")
          return $ xv `sEq` (SApp [vk, vn])
      TDH_PK n -> do
          vn <- symNameExp n
          dhpk <- getTopLevelFunc ("dhpk")
          return $ xv `sEq` (SApp [dhpk, vn])
      TEnc_PK n -> do
          vn <- symNameExp n
          encpk <- getTopLevelFunc ("enc_pk")
          return $ xv `sEq` (SApp [encpk, vn])
      TKEM_PK n -> do
          vn <- symNameExp n
          encpk <- getTopLevelFunc ("kem_pk")
          return $ xv `sEq` (SApp [encpk, vn])
      TSS n m -> do
          vn <- symNameExp n
          vm <- symNameExp m
          dhpk <- getTopLevelFunc ("dhpk")
          dh_combine <- getTopLevelFunc ("dh_combine")
          return $ xv `sEq` (SApp [dh_combine, SApp [dhpk, vn], vm])
      TUnit -> return $ xv `sHasType` (SAtom "Unit")
      TAdmit -> return $ sTrue
      TCase p t1 t2 -> do
          vp <- interpretProp p
          vt1 <- smtTy xv t1
          vt2 <- smtTy xv t2
          return $ (sImpl vp vt1) `sAnd2` (sImpl (sNot vp) vt2)
      TExistsIdx _ bt -> do
          (i, t0) <- liftCheck $ unbind bt
          s <- withSMTIndices [(i, IdxGhost)] $ smtTy xv t0
          let iname = cleanSMTIdent $ show i
          return $ sExists [(SAtom iname, indexSort)] s [] $ "TExists_" ++ iname
      TConst s@(PRes (PDot pth _)) ps -> do
          td <- liftCheck $ getTyDef  s
          case td of
            TyAbstract -> return sTrue
            TyAbbrev t -> smtTy xv t
            StructDef ixs -> smtStructRefinement ps pth ixs xv
            EnumDef ixs -> do
                dts <- liftCheck $ extractEnum ps (show s) ixs
                let ts = map (\(_, ot) -> case ot of
                                              Just t -> t
                                              Nothing -> tUnit) dts
                sMkEnumCond xv ts
      THexConst a -> do
          h <- makeHex a
          return $ xv `sEq` h 

sMkEnumCond :: SExp -> [Ty] -> Sym SExp
sMkEnumCond xv ts = do
    liftCheck $ assert ("sMkEnumCond: tys must be non-null") $ length ts > 0
    let tag = SApp [SAtom "Prefix", xv, SAtom "2"]
    let payload = SApp [SAtom "Postfix", xv, SAtom "2"]
    let p1 = SApp [SAtom "OkInt", tag]
    let p2 = SApp [SAtom ">=", SApp [SAtom "B2I", sLength xv], SAtom "2"]
    let p3 = SApp [SAtom "<", SApp [SAtom "B2I", tag], SAtom (show $ length ts)]
    conds <- forM [0 .. (length ts - 1)] $ \i -> do
        tv <- smtTy payload (ts !! i)
        return $ sImpl (sEq (SApp [SAtom "B2I", tag]) (SAtom $ show i)) tv
    return $ sAnd $ p1 : p2 : p3 : conds
                    



smtStructRefinement :: [FuncParam] -> ResolvedPath -> Bind [IdxVar] (DepBind ()) -> SExp -> Sym SExp
smtStructRefinement fps spath idp structval = do 
    (is, dp) <- liftCheck $ unbind idp
    idxs <- liftCheck $ getStructParams fps
    liftCheck $ assert ("Wrong index arity for struct") $ length is == length idxs
    (ps, lengths) <- go $ substs (zip is idxs) dp
    let len = case lengths of
                [] -> SApp [SAtom "I2B", SAtom "0"]
                _ -> foldr1 (\x y -> SApp [SAtom "plus", x, y]) lengths
    let length_refinement = 
            sEq (sLength structval) 
                len
    return $ sAnd $ ps ++ [length_refinement]
        where
            -- First list is type refinements, second is list of lengths.
            -- This list of lengths skips over ghost types
            go :: DepBind () -> Sym ([SExp], [SExp])
            go (DPDone _) = error "unreachable"
            go (DPVar t sx xk) = do
                sn <- smtName $ PDot spath sx
                let fld = SApp [SAtom sn, structval]
                vt1 <- smtTy fld t
                tNonGhost <- liftCheck $ tyNonGhost t
                let l = case tNonGhost of 
                          True -> [sLength fld]
                          False -> []
                let plength1 = ([vt1], l)
                (x, k) <- liftCheck $ unbind xk
                case k of
                  DPDone _ -> return plength1
                  _ -> do 
                      (p2, lengths2) <- withSMTVars' [(x, fld)] $ go k
                      return $ (fst plength1 ++ p2, snd plength1 ++ lengths2)
            

sTypeSeq :: [SExp] -> SExp
sTypeSeq [] = SAtom "(as seq.empty (Seq Type))"
sTypeSeq (x:xs) = SApp [SAtom "seq.++", SApp [SAtom "seq.unit", x], sTypeSeq xs]

sHasType :: SExp -> SExp -> SExp
sHasType v vt = SApp [SAtom "HasType", v, vt]

tyConstraints :: Ty -> SExp -> Sym SExp
tyConstraints t v = smtTy v t
    
subTypeCheck :: Ty -> Ty -> Sym ()
subTypeCheck t1 t2 = pushRoutine ("subTypeCheck(" ++ show (tupled $ map owlpretty [t1, t2]) ++ ")") $ do
    v <- mkTy Nothing t1
    c <- tyConstraints t2 v
    emitComment $ T.pack "Checking subtype " <> optext t1 <> T.pack " <= " <> optext t2
    emitToProve c

sConcats :: [SExp] -> SExp
sConcats vs = 
    let sConcat a b = SApp [SAtom "concat", a, b] in
    foldl sConcat (head vs) (tail vs) 

symListUniq :: [AExpr] -> Sym ()
symListUniq es = do
    vs <- mapM interpretAExp es
    emitComment $ T.pack "Proving symListUniq with es = " <> optext es 
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
        emitComment $ T.pack "Checking if " <> optext es <> T.pack " equals ghost val " <> optext eghosts 
        emitToProve $ sAnd $ map (\(x, y) -> sEq x y) $ zip v_es v_eghosts 

symAssert :: Prop -> Sym ()
symAssert p = pushRoutine ("symAssert(" ++ show (owlpretty p) ++ ")") $ do
    b <- interpretProp p
    emitComment $ T.pack $ "Proving prop " ++ show (owlpretty p)
    emitToProve b

symDecideProp :: Prop -> Check (Maybe String, Maybe Bool) 
symDecideProp p = do
    let k1 = do {
        emitComment $ T.pack $ "Trying to prove prop " ++ show (owlpretty p);
        b <- interpretProp p;
        emitToProve b 
                }
    let k2 = do {
        emitComment $ T.pack $ "Trying to prove prop " ++ show (owlpretty $ pNot p);
        b <- interpretProp $ pNot p;
        emitToProve b 
                }
    raceSMT initSolverEnv smtSetup k2 k1

initSolverEnv = initSolverEnv_ symLabel

checkFlows :: Label -> Label -> Check (Maybe String, Maybe Bool)
checkFlows l1 l2 = do
    let k1 = do {
        emitComment $ T.pack $ "Trying to prove " ++ show (owlpretty l1) ++ " <= " ++ show (owlpretty l2);
        x <- symLabel l1;
        y <- symLabel l2;
        emitToProve $ SApp [SAtom "Flows", x, y]
                }
    let k2 = do {
        emitComment $ T.pack $ "Trying to prove " ++ show (owlpretty l1) ++ " !<= " ++ show (owlpretty l2);
        x <- symLabel l1;
        y <- symLabel l2;
        emitToProve $ sNot $ SApp [SAtom "Flows", x, y]
                }
    raceSMT initSolverEnv smtSetup k2 k1



