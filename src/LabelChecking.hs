{-# LANGUAGE FlexibleInstances, DeriveGeneric, ScopedTypeVariables #-}
module LabelChecking where 
import qualified Data.Map.Strict as M
import qualified Data.Map.Ordered as OM
import qualified Data.Set as S
import Prettyprinter
import AST 
import Control.Lens
import SMTBase
import Pretty
import TypingBase
import Control.Monad
import Control.Monad.Reader
import Unbound.Generics.LocallyNameless
import qualified Data.Text as T
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import Data.List (sort)

instance Fresh Sym where
    fresh x = liftCheck $ fresh x


sFlows :: SExp -> SExp -> SExp
sFlows x y = SApp [SAtom "Flows", x, y]

sJoin :: SExp -> SExp -> SExp
sJoin x y = SApp [SAtom "Join", x, y]

removeGhost :: Label -> Check Label
removeGhost l = 
    case l^.val of
      LGhost -> return zeroLbl
      LJoin l1 l2 -> liftM2 (\a b -> Spanned (l^.spanOf) (LJoin a b)) (removeGhost l1) (removeGhost l2)
      LConst _ -> return l
      LRangeIdx il -> do
          (i, l2) <- unbind il
          l2' <- removeGhost l2
          return $ Spanned (l^.spanOf) $ LRangeIdx $ bind i l2'
      LRangeVar il -> do
          (i, l2) <- unbind il
          l2' <- removeGhost l2
          return $ Spanned (l^.spanOf) $ LRangeVar $ bind i l2'
      LName _ -> return l
      LAdv -> return l
      LZero -> return l
      LTop -> return l

nameDefFlows :: NameExp -> NameType -> Sym SExp
nameDefFlows n nt = do
    case nt^.val of 
      NT_KEM _ -> do
          i <- freshSMTIndexName
          ctr <- getFreshCtr
          ln <- symLabel $ mkSpanned $ LName n
          (ax, l) <- withSMTIndices [(s2n i, IdxGhost)] $ do
              l <- symLabel $ mkSpanned $ LName $ mkSpanned $ KEMName n (mkIVar $ s2n i)
              return $ (sFlows l ln, l)
          return $ sForall [(SAtom i, indexSort)] ax [l] ("ax_" ++ show ctr)
      NT_App p is -> (liftCheck $ resolveNameTypeApp p is) >>= nameDefFlows n
      NT_Nonce _ -> return sTrue
      NT_DH -> return sTrue
      NT_Enc t -> do
          l <- liftCheck $ coveringLabel' t >>= removeGhost
          lv <- symLabel l
          ln <- symLabel $ mkSpanned $ LName n
          return $ sFlows lv ln
      NT_StAEAD t _ _ _ -> do
          l <- liftCheck $ coveringLabel' t >>= removeGhost
          lv <- symLabel l
          ln <- symLabel $ mkSpanned $ LName n
          return $ sFlows lv ln
      NT_PKE t -> do
          l <- liftCheck $ coveringLabel' t  >>= removeGhost
          lv <- symLabel l
          ln <- symLabel $ mkSpanned $ LName n
          return $ sFlows lv ln
      NT_Sig t -> do
          l <- liftCheck $ coveringLabel' t >>= removeGhost
          lv <- symLabel l
          ln <- symLabel $ mkSpanned $ LName n
          return $ sFlows lv ln
      NT_MAC t -> do
          l <- liftCheck $ coveringLabel' t >>= removeGhost
          lv <- symLabel l
          ln <- symLabel $ mkSpanned $ LName n
          return $ sFlows lv ln
      NT_KDF pos bnd -> do 
          ctr <- getFreshCtr
          (((sx, x), (sy, y), (sz, z)), cases) <- liftCheck $ unbind bnd
          -- TODO: below, we need to generealize
          axs <- withSMTVars [x, y, z] $ do
              axis <- forM [0 .. (length cases - 1)] $ \i -> do
                  (ixs, (p, nts)) <- liftCheck $ unbind $ cases !! i
                  axijs <- forM [0 .. (length nts - 1)] $ \j -> do
                      let (strictness, nt) = nts !! j
                      ne_axioms <- withSMTIndices (map (\i -> (i, IdxGhost)) ixs) $ do
                          nks <- liftCheck $ mapM (\(_, nt) -> getNameKind nt) nts
                          let ne = case pos of 
                                     KDF_SaltPos -> 
                                         mkSpanned $ KDFName (mkSpanned $ AEGet n) (aeVar' x) (aeVar' y) nks j nt (ignore True)
                                     KDF_IKMPos -> 
                                         mkSpanned $ KDFName (aeVar' x) (mkSpanned $ AEGet n) (aeVar' y) nks j nt (ignore True)
                          nameDefFlows ne nt
                      ctr <- getFreshCtr
                      vp <- interpretProp p
                      return $ sForall (map (\i -> (SAtom $ cleanSMTIdent $ show i, indexSort)) ixs) 
                                (sImpl vp ne_axioms)
                                []
                                ("ax_" ++ show ctr)
                  return $ sAnd axijs
              return $ sAnd axis
          let vx = SAtom (show x)
          let vy = SAtom (show y)
          return $ sForall [(vx, bitstringSort), (vy, bitstringSort)] axs [] ("kdfFlows_" ++ show ctr)

smtLabelSetup :: Sym ()
smtLabelSetup = do
    -- Flow axioms for abstract types
    fas <- liftCheck $ collectFlowAxioms
    forM_ fas $ \(l1, l2) -> do
        v1 <- symLabel l1
        v2 <- symLabel l2
        emitComment $ T.pack $ "Flow decl: " ++ show (owlpretty l1) ++ " <= " ++ show (owlpretty l2)
        emitAssertion $ sFlows v1 v2
    
    -- Constraints on the adv
    afcs <- liftCheck $ collectAdvCorrConstraints 
    forM_ (zip afcs [0 .. (length afcs - 1)]) $ \(ils, j) -> do 
        ((is, xs), cc) <- liftCheck $ unbind ils
        withSMTIndices (map (\i -> (i, IdxGhost)) is) $ do
            withSMTVars xs $ do 
                scc <- mkCorrConstraint cc
                emitAssertion $ sForall 
                    (map (\i -> (SAtom $ show i, indexSort)) is ++ map (\x -> (SAtom $ show x, bitstringSort)) xs)
                    scc
                    []
                    ("advConstraint_" ++ show j)

mkCorrConstraint :: CorrConstraint -> Sym SExp
mkCorrConstraint (CorrImpl l1 l2) = do
    ladv <- symLabel advLbl
    v1 <- symLabel l1
    v2 <- symLabel l2
    return $ sImpl (sFlows v1 ladv) (sFlows v2 ladv)
mkCorrConstraint (CorrGroup ls) = do
    ladv <- symLabel advLbl
    vls <- mapM symLabel ls
    let vgroup = sJoins vls 
    let ccs = map (\v -> sImpl (sFlows v ladv) (sFlows vgroup ladv)) vls
    return $ sAnd ccs

getIdxVars :: Label -> [IdxVar]
getIdxVars l = toListOf fv l

-- Simplify the label, floating /\ above /\_i, removing /\_i if i is not used
simplLabel :: Label -> Check Label
simplLabel l = 
    case l^.val of
      LName n -> return l
      LZero -> return l
      LAdv -> return l
      LTop -> return l
      LGhost -> return l
      LConst _ -> return l
      LJoin l1 l2 -> liftM2 joinLbl (simplLabel l1) (simplLabel l2)
      LRangeVar _ -> return l
      LRangeIdx il -> do
          (i, l') <- unbind il
          if i `elem` getIdxVars l' then 
            do
                l'' <- simplLabel l'
                case l''^.val of
                    LJoin l1 l2 ->
                        simplLabel $ joinLbl (mkSpanned $ LRangeIdx $ bind i l1) (mkSpanned $ LRangeIdx $ bind i l2)
                    _ -> return $ mkSpanned $ LRangeIdx $ bind i l''
          else simplLabel l'


canonNoBig :: CanonAtom -> CanonLabelBig
canonNoBig x = CanonBig $ bind ([], []) x

-- Canonizes the label, assuming it has been simplified
-- 
canonLabel :: Label -> Sym CanonLabel
canonLabel l = do
    case l^.val of
      LJoin l1 l2 -> do
          (CanonAnd c1) <- canonLabel l1
          (CanonAnd c2) <- canonLabel l2
          return $ CanonAnd $ c1 ++ c2
      LName ne -> return $ CanonAnd [canonNoBig $ CanonLName ne]
      LZero -> return $ CanonAnd [canonNoBig $ CanonZero]
      LAdv -> return $ CanonAnd [canonNoBig $ CanonAdv]
      LTop -> return $ CanonAnd [canonNoBig $ CanonTop]
      LGhost -> return $ CanonAnd [canonNoBig $ CanonGhost]
      LConst s -> return $ CanonAnd [canonNoBig $ CanonConst s]
      LRangeIdx il -> do 
          (i, l') <- liftCheck $ unbind il
          ((is, xs), l) <- canonRange [i] [] l'
          return $ CanonAnd [CanonBig $ bind (sort is, sort xs) l]
      LRangeVar xl -> do 
          (x, l') <- liftCheck $ unbind xl
          ((is, xs), l) <- canonRange [] [x] l'
          return $ CanonAnd [CanonBig $ bind (sort is, sort xs) l]

canonRange :: [IdxVar] -> [DataVar] -> Label -> Sym (([IdxVar], [DataVar]), CanonAtom)       
canonRange is xs l = 
    case l^.val of
      LJoin _ _ -> error "Internal error: should not get join inside big"
      LRangeIdx il' -> do
          (i, l') <- liftCheck $ unbind il'
          canonRange (i : is) xs l'
      LRangeVar xl' -> do
          (x, l') <- liftCheck $ unbind xl'
          canonRange is (x : xs) l'
      LZero -> return ((is, xs), CanonZero)
      LAdv -> return ((is, xs), CanonAdv)
      LTop -> return ((is, xs), CanonTop)
      LConst s -> return ((is, xs), CanonConst s)
      LName ne -> return ((is, xs), CanonLName ne)


sJoins :: [SExp] -> SExp
sJoins [] = SAtom "%zeroLbl"
sJoins xs = foldr1 sJoin xs

symCanonLabel :: CanonLabel -> Sym SExp
symCanonLabel (CanonAnd xs) = do
    vs <- mapM symCanonBig xs
    return $ sJoins vs

symCanonBig :: CanonLabelBig -> Sym SExp
symCanonBig c = do
    lvs <- use labelVals
    case M.lookup (AlphaOrd c) lvs of
      Just v -> return v
      Nothing -> do
        v <- case c of
              CanonBig ixl -> do
                  ((is, xs), l) <- liftCheck $ unbind ixl
                  let bnd_rel = any (\x -> x `elem` toListOf fv l) is || any (\x -> x `elem` toListOf fv l) xs
                  case bnd_rel of
                    False -> symCanonAtom l
                    True -> do
                        x <- freshSMTName
                        emit $ SApp [SAtom "declare-const", SAtom x, SAtom "Label"]
                        ivs <- mapM (\_ -> freshSMTIndexName) is
                        xvs <- mapM (\_ -> freshSMTIndexName) xs
                        lv <- withSMTIndices (map (\iv -> (s2n iv, IdxGhost)) ivs) $ 
                            withSMTVars (map s2n xvs) $
                                symCanonAtom $ substs (zip is (map (mkIVar . s2n) ivs)) $ substs (zip xs (map (aeVar' . s2n) xvs)) l
                        emitAssertion $ sForall (map (\i -> (SAtom i, indexSort)) ivs ++ map (\x -> (SAtom x, bitstringSort)) xvs)
                                                (sFlows lv (SAtom x)) [] ("big_" ++ x)
                        return $ SAtom x
        labelVals %= M.insert (AlphaOrd c) v
        return v




symCanonAtom :: CanonAtom -> Sym SExp
symCanonAtom c = 
    case c of
      CanonLName ne -> do
        n <- getSymName ne
        return $ SApp [SAtom "LabelOf", n]
      CanonZero -> return $ SAtom "%zeroLbl"
      CanonAdv -> return $ SAtom "%adv"
      CanonTop -> return $ SAtom "%top"
      CanonGhost -> return $ SAtom "%ghost"
      CanonConst s -> getSymLblConst s

getSymLblConst :: LblConst -> Sym SExp
getSymLblConst (TyLabelVar n@(PRes p)) = do
    e <- use symLabelVarEnv
    case M.lookup (AlphaOrd p) e of
      Just res -> return res
      Nothing -> do
          sp <- smtName p
          let sname = SAtom $ "%lvar_" ++ sp
          emit $ SApp [SAtom "declare-fun", sname, SApp [], SAtom "Label"]
          emitAssertion $ sFlows (SAtom "%adv") sname
          symLabelVarEnv %= (M.insert (AlphaOrd p) sname)
          return sname


symLabel :: Label -> Sym SExp
symLabel l = do
    l' <- liftCheck $ simplLabel l
    c <- canonLabel l'
    symCanonLabel c

data SymLbl = 
    SName NameExp
      | SConst LblConst
      | SAdv
      | STop
      | SGhost
      | SRange (Bind IdxVar SymLbl)
      deriving (Show, Generic, Typeable)

instance Alpha SymLbl

mkSymLbl :: Label -> Check (S.Set (AlphaOrd SymLbl))
mkSymLbl l = 
    case l^.val of
      LZero -> return S.empty
      LName n -> return $ S.singleton $ AlphaOrd $ SName n
      LConst s -> return $ S.singleton $ AlphaOrd $ SConst s
      LAdv -> return $ S.singleton $ AlphaOrd SAdv
      LTop -> return $ S.singleton $ AlphaOrd STop
      LGhost -> return $ S.singleton $ AlphaOrd SGhost
      LJoin x y -> liftM2 S.union (mkSymLbl x) (mkSymLbl y)
      LRangeVar xl -> do
          (xi, l) <- unbind xl
          if xi `elem` toListOf fv l then 
                                   typeError $ "Trying to simplify label containing range over bv"
                                   else mkSymLbl l
      LRangeIdx xl -> do
          (xi, l) <- unbind xl
          if xi `elem` getIdxVars l then  do
              l' <- mkSymLbl l
              return $ S.map (\l -> AlphaOrd $ SRange $ bind xi (_unAlphaOrd l)) l'
          else mkSymLbl l


lblFromSym :: SymLbl -> Check Label
lblFromSym s = 
    case s of
      SName n -> return $ nameLbl n
      SAdv -> return advLbl
      STop -> return topLbl
      SGhost -> return ghostLbl
      SConst n -> return $ lblConst n
      SRange xl -> do
          (x, l) <- unbind xl
          l' <- lblFromSym l
          return $ mkSpanned $ LRangeIdx $ bind x l'

joinLbls :: [Label] -> Label
joinLbls [] = zeroLbl
joinLbls xs = foldr1 joinLbl xs

lblFromSym' :: S.Set (AlphaOrd SymLbl) -> Check Label
lblFromSym' s = do
    xs <- mapM lblFromSym $ map _unAlphaOrd $ S.toList s
    return $ joinLbls xs

normLabel :: Label -> Check Label
normLabel l = do
    l' <- simplLabel l
    s <- mkSymLbl l'
    lblFromSym' s



