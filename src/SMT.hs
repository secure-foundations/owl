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

smtTypingQuery s = fromSMT s smtSetup

setupSMTOptions :: Sym ()
setupSMTOptions = do
    o <- view $ z3Options
    forM_ (M.assocs o) $ \(k, v) -> do
        emit $ SApp [SAtom "set-option", SAtom k, SAtom v]

setupIndexEnv :: Sym ()
setupIndexEnv = do
    inds <- view $ inScopeIndices
    assocs <- forM (map fst inds) $ \i -> do
        x <- freshIndexVal (cleanSMTIdent $ show i)
        return (i, x)
    symIndexEnv .= M.fromList assocs

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
                            ("nameKind_" ++ show sn)

                        let nameExp = mkSpanned $ NameConst (map (\x -> IVar (ignore def) (ignore $ show x) x) is, map (\x -> IVar (ignore def) (ignore $ show x) x) ps) (PRes pth) 

                        lAxs <- nameDefFlows nameExp nt
                        emitAssertion $ sForall (ivs)
                            lAxs
                            [sApp (sn : (map fst ivs))]
                            ("nameDefFlows_" ++ show sn)
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
                emitAssertion $ sForall (q1 ++ q2) (sNot $ v1_eq_v2) pat $ "disj_" ++ show (sn1) ++ "_" ++ show (sn2) 
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
                        [v1_eq_v2]
                        ("self_disj_" ++ show (sn))








mkTy :: Maybe String -> Ty -> Sym SExp
mkTy s t = do
    x <- freshSMTVal (case s of
                     Nothing -> Nothing
                     Just x -> Just $ x ++ " : " ++ show (owlpretty t)
                  )
    c <- tyConstraints t x
    emitComment $ "ty constraint for " ++ show x ++ ": " ++ show (owlpretty t)
    emitAssertion c
    return x

setupTyEnv :: Sym ()
setupTyEnv = do
    vE <- view tyContext
    go vE
    where
        go [] = return ()
        go ((x, (_, _, t)) : xs) = do
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
builtInSMTFuncs = ["length", "eq", "plus", "mult", "UNIT", "true", "false", "andb", "concat", "zero", "dh_combine", "dhpk", "is_group_elem", "crh"]

mkPred :: Path -> Sym SExp  
mkPred pth@(PRes (PDot p s)) = do
    pis <- use predInterps
    sn <- smtName pth
    case M.lookup sn pis of
      Just v -> return v
      Nothing ->  do
          md <- liftCheck $ openModule p
          case lookup s (md^.predicates) of
            Nothing -> error $ "Predicate " ++ show pth ++ " not found. " 
            Just b -> do
                ((ixs, xs), pr) <- liftCheck $ unbind b
                let ivs = map (\i -> (SAtom (show i), indexSort)) ixs
                let xvs = map (\x -> (SAtom (show x), bitstringSort)) xs
                withSMTIndices (map (\i -> (i, IdxGhost)) ixs) $ 
                    withSMTVars xs $ do
                        v <- interpretProp pr
                        emit $ SApp [SAtom "declare-fun", SAtom sn, SApp (replicate (length ixs) indexSort ++ replicate (length xs) bitstringSort), SAtom "Bool"]
                        let ax = sForall
                                    (ivs ++ xvs)
                                    (SApp [SAtom "=", sApp (SAtom sn : (map fst ivs) ++ (map fst xvs)), v])
                                    [sApp (SAtom sn : (map fst ivs) ++ (map fst xvs))]
                                    ("predDef_" ++ sn)
                        emitAssertion $ ax
                        return ()
                predInterps %= (M.insert sn (SAtom sn))
                return $ SAtom sn

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

sLambda :: (SExp -> SExp) -> SExp
sLambda k = 
    let x = SAtom "%x" in
    SApp [SAtom "lambda", SApp [SApp [x, SAtom "Bits"]], k x]

sLambdaExplicit :: SExp -> SExp -> SExp -> SExp
sLambdaExplicit x sort bdy = SApp [SAtom "lambda", SApp [SApp [x, sort]], bdy]

sRefined :: SExp -> (SExp -> SExp) -> SExp
sRefined v k = 
    SApp [SAtom "Refined", v, sLambda k]

sRefined' :: SExp -> (SExp -> Sym SExp) -> Sym SExp
sRefined' v k = do
    x <- SAtom <$> freshSMTName
    vk <- k x
    return $ SApp [SAtom "Refined", v, SApp [SAtom "lambda", SApp [SApp [x, SAtom "Bits"]], vk]] 

smtTy :: Ty -> Sym SExp
smtTy t = 
    case t^.val of
      TData _ _ _ -> return $ SAtom "Data"
      TGhost -> return $ SAtom "Data"
      TDataWithLength _ a -> do
          v <- interpretAExp a
          return $ sRefined (SAtom "Data") $ \x -> (sLength x) `sEq` v
      TBool _ -> return $ SAtom "TBool"  
      TRefined t s xp -> do
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
          td <- liftCheck $ getTyDef  s
          case td of
            TyAbstract -> return $ SAtom "Data"
            TyAbbrev t -> smtTy t
            StructDef ixs -> sRefined' (SAtom "Data") $ \x -> smtStructRefinement ps pth ixs x
            EnumDef ixs -> do
                dts <- liftCheck $ extractEnum ps (show s) ixs
                vts <- forM dts $ \(_, ot) -> 
                    case ot of
                      Just t -> smtTy t
                      Nothing -> return $ SAtom "Unit"
                return $ sEnumType vts
      THexConst a -> do
          h <- makeHex a
          return $ sRefined (SAtom "Data") $ \x -> x `sEq` h 

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
                vt1 <- smtTy t
                sn <- smtName $ PDot spath sx
                let fld = SApp [SAtom sn, structval]
                let l = case (stripRefinements t)^.val of
                          TGhost -> []
                          _ -> [sLength fld]
                let plength1 = ([fld `sHasType` vt1], l)
                (x, k) <- liftCheck $ unbind xk
                case k of
                  DPDone _ -> return plength1
                  _ -> do 
                      (p2, lengths2) <- withSMTVars' [(x, fld)] $ go k
                      return $ (fst plength1 ++ p2, snd plength1 ++ lengths2)
            

sTypeSeq :: [SExp] -> SExp
sTypeSeq [] = SAtom "(as seq.empty (Seq Type))"
sTypeSeq (x:xs) = SApp [SAtom "seq.++", SApp [SAtom "seq.unit", x], sTypeSeq xs]

sEnumType :: [SExp] -> SExp
sEnumType xs = SApp [SAtom "Enum", sTypeSeq xs]

sHasType :: SExp -> SExp -> SExp
sHasType v vt = SApp [SAtom "HasType", v, vt]

tyConstraints :: Ty -> SExp -> Sym SExp
tyConstraints t v = do
    vt <- smtTy t
    return $ SApp [SAtom "HasType", v, vt]






interpretProp :: Prop -> Sym SExp
interpretProp p = do
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
      PLetIn a xp -> do
          (x, p) <- liftCheck $ unbind xp
          interpretProp $ subst x a p
      PApp s is ps -> do 
          vs <- mkPred s 
          ixs <- mapM symIndex is
          vps <- mapM interpretAExp ps
          return $ sApp (vs : ixs ++ vps)
      PAADOf ne a -> do
          p <- liftCheck $ extractAAD ne a
          interpretProp p
      (PEq p1 p2) -> do
          v1 <- interpretAExp p1
          v2 <- interpretAExp p2
          return $ SApp [SAtom "=", SAtom "TRUE", SApp [SAtom "eq", v1, v2]]
      (PValidKDF a b c nks j) -> do
          va <- interpretAExp a
          vb <- interpretAExp b
          vc <- interpretAExp c
          nk_lengths <- liftCheck $ forM nks $ \nk -> sNameKindLength <$> smtNameKindOf nk
          let start = sPlus $ take j nk_lengths
          let segment = nk_lengths !! j
          return $ SApp [SAtom "ValidKDF", va, vb, vc, start, segment, SAtom (show $ nks !! j)]
      (PEqIdx i1 i2) ->
        liftM2 (sEq) (symIndex i1) (symIndex i2)
      (PIsConstant a) -> do
          v <- interpretAExp a
          return $ SApp [SAtom "IsConstant", v]
      (PQuantBV q _ ip) -> do
          (x, p) <- liftCheck $ unbind ip
          v <- withSMTVars [x] $ interpretProp p 
          let xname = cleanSMTIdent $ show x
          case q of
            Forall -> return $ sForall [(SAtom xname, bitstringSort)] v [] $ "forall_" ++ xname
            Exists -> return $ sExists [(SAtom xname, bitstringSort)] v [] $ "exists_" ++ xname
      (PQuantIdx q _ ip) -> do
          (i, p') <- liftCheck $ unbind ip
          v <- withSMTIndices [(i, IdxGhost)] $ interpretProp p'
          let iname = cleanSMTIdent $ show i
          case q of
            Forall -> return $ sForall [(SAtom iname, indexSort)] v [] $ "forall_" ++ iname 
            Exists -> return $ sExists [(SAtom iname, indexSort)] v [] $ "exists_" ++ iname
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
subTypeCheck t1 t2 = pushRoutine ("subTypeCheck(" ++ show (tupled $ map owlpretty [t1, t2]) ++ ")") $ do
    v <- mkTy Nothing t1
    c <- tyConstraints t2 v

    emitComment $ "Checking subtype " ++ show (owlpretty t1) ++ " <= " ++ show (owlpretty t2)
    emitToProve c

sConcats :: [SExp] -> SExp
sConcats vs = 
    let sConcat a b = SApp [SAtom "concat", a, b] in
    foldl sConcat (head vs) (tail vs) 

symListUniq :: [AExpr] -> Sym ()
symListUniq es = do
    vs <- mapM interpretAExp es
    emitComment $ "Proving symListUniq with es = " ++ show (owlpretty es)
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
        emitComment $ "Checking if " ++ show (owlpretty es) ++ " equals ghost val " ++ show (owlpretty eghosts) 
        emitToProve $ sAnd $ map (\(x, y) -> sEq x y) $ zip v_es v_eghosts 

symAssert :: Prop -> Sym ()
symAssert p = pushRoutine ("symAssert(" ++ show (owlpretty p) ++ ")") $ do
    b <- interpretProp p
    emitComment $ "Proving prop " ++ show (owlpretty p)
    emitToProve b

disjointProps :: [Prop] -> Sym ()
disjointProps ps = do
    vps <- mapM interpretProp ps
    emitToProve $ sAtMostOne vps

symEqNameExp :: NameExp -> NameExp -> Check Bool
symEqNameExp ne1 ne2 = do
    (_, b) <- smtTypingQuery "symEqNameExp" $ do
        s1 <- symNameExp ne1
        s2 <- symNameExp ne2
        emitToProve $ sEq s1 s2 
    return b


symDecideProp :: Prop -> Check (Maybe String, Maybe Bool) 
symDecideProp p = do
    let k1 = do {
        emitComment $ "Trying to prove prop " ++ show (owlpretty p);
        b <- interpretProp p;
        emitToProve b 
                }
    let k2 = do {
        emitComment $ "Trying to prove prop " ++ show (owlpretty $ pNot p);
        b <- interpretProp $ pNot p;
        emitToProve b 
                }
    raceSMT smtSetup k2 k1

checkFlows :: Label -> Label -> Check (Maybe String, Maybe Bool)
checkFlows l1 l2 = do
    let k1 = do {
        emitComment $ "Trying to prove " ++ show (owlpretty l1) ++ " <= " ++ show (owlpretty l2);
        x <- symLabel l1;
        y <- symLabel l2;
        emitToProve $ SApp [SAtom "Flows", x, y]
                }
    let k2 = do {
        emitComment $ "Trying to prove " ++ show (owlpretty l1) ++ " !<= " ++ show (owlpretty l2);
        x <- symLabel l1;
        y <- symLabel l2;
        emitToProve $ sNot $ SApp [SAtom "Flows", x, y]
                }
    raceSMT smtSetup k2 k1



