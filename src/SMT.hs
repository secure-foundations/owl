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

smtTypingQuery s = fromSMT initSolverEnv s smtSetup

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

                        let nameExp = mkSpanned $ NameConst (map (\x -> IVar (ignore def) (ignore $ show x) x) is, map (\x -> IVar (ignore def) (ignore $ show x) x) ps) (PRes pth) [] 

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
                        [v1, v2]
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
builtInSMTFuncs = ["length", "eq", "plus", "mult", "UNIT", "true", "false", "andb", "concat", "zero", "dh_combine", "dhpk", "is_group_elem", "crh", "xor"]


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

kdfPerm va vb vc start segment nt_ = do
    nt <- liftCheck $ normalizeNameType nt_
    permctr <- use kdfPermCounter
    case M.lookup (AlphaOrd nt) permctr of
      Just nv -> return $ SApp [SAtom "KDFPerm", va, vb, vc, start, segment, nv]
      Nothing -> do
          nv <- getFreshCtr
          kdfPermCounter %= M.insert (AlphaOrd nt) (SAtom $ show nv)
          return $ SApp [SAtom "KDFPerm", va, vb, vc, start, segment, (SAtom $ show nv)]



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
          kdfRefinement <- case n^.val of
                             NameConst _ _ _ -> return sTrue
                             KDFName a b c nks j nt -> do 
                                 (va, vb, vc, start, segment) <- getKDFArgs a b c nks j
                                 p <- kdfPerm va vb vc start segment nt
                                 return $ sAnd2 p $ xv `sEq` (SApp [SAtom "KDF", va, vb, vc, start, segment])
          vn <- getSymName n
          return $ sAnd2 kdfRefinement (xv `sHasType` (SApp [SAtom "TName", vn]))
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
      TExistsIdx _ _ -> return $ sTrue -- Opaque to SMT
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
                let l = case (stripRefinements t)^.val of
                          TGhost -> []
                          _ -> [sLength fld]
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
    raceSMT initSolverEnv smtSetup k2 k1

initSolverEnv = initSolverEnv_ symLabel

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
    raceSMT initSolverEnv smtSetup k2 k1



