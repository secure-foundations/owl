{-# LANGUAGE FlexibleInstances, DeriveGeneric, ScopedTypeVariables #-}
module LabelChecking where 
import qualified Data.Map.Strict as M
import qualified Data.Map.Ordered as OM
import qualified Data.Set as S
import Prettyprinter
import AST 
import Control.Lens
import SMTBase
import TypingBase
import Control.Monad
import Control.Monad.Reader
import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import Data.List (sort)

instance Fresh Sym where
    fresh x = liftCheck $ fresh x


sFlows :: SExp -> SExp -> SExp
sFlows x y = SApp [SAtom "Flows", x, y]

sJoin :: SExp -> SExp -> SExp
sJoin x y = SApp [SAtom "Join", x, y]


-- If the random oracle value is a secret, then one of the arguments is a
-- secret.
-- N.B.: this list does _not_ have to be exhaustive. It is only used to
-- prune impossible paths
solvabilityAxioms :: ResolvedPath -> Bind [IdxVar] ([AExpr], [NameType]) -> Sym SExp
solvabilityAxioms n bnd = do
    sname <- smtName n
    ladv <- symLabel advLbl
    (is, (aes, nts)) <- liftCheck $ unbind bnd
    sIE <- use symIndexEnv
    symIndexEnv  %= (M.union $ M.fromList $ map (\i -> (i, SAtom $ show i)) is)
    res <- local (over inScopeIndices $ (++) $ map (\i -> (i, IdxGhost)) is) $ do
        -- The labels which must be secret for the RO to be secret
        lss <- forM aes $ \ae -> do
            t <- liftCheck $ inferAExpr ae
            case t^.val of
              TName n -> return [nameLbl n]
              TSS n m -> return [nameLbl n, nameLbl m]
              _ -> return []
        lvs <- mapM symLabel $ concat lss
        i <- SAtom <$> freshSMTName
        let vro = sROName (SAtom $ "%ro_" ++ sname) (map (SAtom . show) is) i
        let vro_sec = map (\l -> sNot $ sFlows l ladv) lvs
        return $ sForall ((i, SAtom "Int") : map (\i -> (SAtom $ show i, indexSort)) is)
                         (sImpl (sNot $ sFlows (SApp [SAtom "LabelOf", vro]) ladv)
                         (sAnd vro_sec))
                         [vro]
    symIndexEnv .= sIE
    return res

nameDefFlows :: NameExp -> NameType -> Sym [(Label, Label)]
nameDefFlows n nt = do
    case nt^.val of 
      NT_Nonce -> return []
      NT_DH -> return []
      NT_Enc t -> do
          l <- liftCheck $ coveringLabel' t
          return $ [(l, mkSpanned $ LName n)]
      NT_EncWithNonce t _ _ -> do
          l <- liftCheck $ coveringLabel' t
          return $ [(l, mkSpanned $ LName n)]
      NT_PKE t -> do
          l <- liftCheck $ coveringLabel' t
          return $ [(l, mkSpanned $ LName n)]
      NT_Sig t -> do
          l <- liftCheck $ coveringLabel' t
          return $ [(l, mkSpanned $ LName n)]
      NT_MAC t -> do
          l <- liftCheck $ coveringLabel' t
          return $ [(l, mkSpanned $ LName n)]
      NT_PRF xs -> do
          ys <- mapM (\(s, (a, nt)) -> nameDefFlows (prfName n s) nt) xs
          let zs  = map (\p -> nameLbl $ prfName n $ fst p) xs
          return $ (concat ys) ++ [(foldr joinLbl zeroLbl zs, mkSpanned (LName n))]


smtLabelSetup :: Sym ()
smtLabelSetup = do
    -- Flow axioms for abstract types
    fas <- liftCheck $ collectFlowAxioms
    forM_ fas $ \(l1, l2) -> do
        v1 <- symLabel l1
        v2 <- symLabel l2
        emitComment $ "Flow decl: " ++ show (pretty l1) ++ " <= " ++ show (pretty l2)
        emitAssertion $ sFlows v1 v2
    
    -- Constraints on the adv
    afcs <- liftCheck $ collectAdvCorrConstraints 
    ladv <- symLabel advLbl
    forM_ afcs $ \ils -> do 
        (is, (l1, l2)) <- liftCheck $ unbind ils
        sIE <- use symIndexEnv
        symIndexEnv  %= (M.union $ M.fromList $ map (\i -> (i, SAtom $ show i)) is)
        local (over inScopeIndices $ (++) $ map (\i -> (i, IdxGhost)) is) $ do 
            v1 <- symLabel l1
            v2 <- symLabel l2
            emitAssertion $ sForall 
                (map (\i -> (SAtom $ show i, indexSort)) is)
                (sImpl (sFlows v1 ladv) (sFlows v2 ladv))
                []
        symIndexEnv .= sIE

    -- Solvability constraints for RO
    emitComment $ "Solvability axioms for RO"
    ros <- liftCheck $ collectRO
    forM_ ros $ \(n, bnd) -> do
        ax <- solvabilityAxioms n bnd
        emitAssertion ax

getIdxVars :: Label -> [IdxVar]
getIdxVars l = toListOf fv l

-- Simplify the label, floating /\ above /\_i, removing /\_i if i is not used
simplLabel :: Label -> Check Label
simplLabel l = 
    case l^.val of
      LName _ -> return l
      LZero -> return l
      LAdv -> return l
      LConst _ -> return l
      LJoin l1 l2 -> liftM2 joinLbl (simplLabel l1) (simplLabel l2)
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



-- Canonizes the label, assuming it has been simplified
-- 
canonLabel :: Label -> Sym CanonLabel
canonLabel l = do
    case l^.val of
      LJoin l1 l2 -> do
          (CanonAnd c1) <- canonLabel l1
          (CanonAnd c2) <- canonLabel l2
          return $ CanonAnd $ c1 ++ c2
      LName ne -> return $ CanonAnd [CanonNoBig $ CanonLName ne]
      LZero -> return $ CanonAnd [CanonNoBig $ CanonZero]
      LAdv -> return $ CanonAnd [CanonNoBig $ CanonAdv]
      LConst s -> return $ CanonAnd [CanonNoBig $ CanonConst s]
      LRangeIdx il -> do 
          (i, l') <- liftCheck $ unbind il
          (is, l) <- canonRange [i] l'
          return $ CanonAnd [CanonBig $ bind (sort is) l]

canonRange :: [IdxVar] -> Label -> Sym ([IdxVar], CanonAtom)       
canonRange is l = 
    case l^.val of
      LJoin _ _ -> error "Internal error: should not get join inside big"
      LRangeIdx il' -> do
          (i, l') <- liftCheck $ unbind il'
          canonRange (i : is) l'
      LZero -> return (is, CanonZero)
      LAdv -> return (is, CanonAdv)
      LConst s -> return (is, CanonConst s)
      LName ne -> return (is, CanonLName ne)


symCanonLabel :: CanonLabel -> Sym SExp
symCanonLabel (CanonAnd xs) = do
    vs <- mapM symCanonBig xs
    return $ foldr sJoin (SAtom "%zeroLbl") vs

symCanonBig :: CanonLabelBig -> Sym SExp
symCanonBig c = do
    lvs <- use labelVals
    case M.lookup (AlphaOrd c) lvs of
      Just v -> return v
      Nothing -> do
        v <- case c of
              CanonNoBig a -> symCanonAtom a
              CanonBig il -> do
                  (is, l) <- liftCheck $ unbind il -- All the i's must be relevant here
                  x <- freshSMTName
                  emitComment $ "label for " ++ show (pretty c)
                  emit $ SApp [SAtom "declare-const", SAtom x, SAtom "Label"]
                  ivs <- mapM (\_ -> freshSMTIndexName) is
                  iEnv <- use symIndexEnv
                  forM_ ivs $ \iv -> 
                      symIndexEnv %= (M.insert (s2n iv) (SAtom iv))
                  lv <- symCanonAtom $ substs (zip is (map (mkIVar . s2n) ivs)) l
                  symIndexEnv .= iEnv
                  emitAssertion $ sForall (map (\i -> (SAtom i, indexSort)) ivs) (sFlows lv (SAtom x)) []
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
      LJoin x y -> liftM2 S.union (mkSymLbl x) (mkSymLbl y)
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
      SConst n -> return $ lblConst n
      SRange xl -> do
          (x, l) <- unbind xl
          l' <- lblFromSym l
          return $ mkSpanned $ LRangeIdx $ bind x l'

lblFromSym' :: S.Set (AlphaOrd SymLbl) -> Check Label
lblFromSym' s = do
    xs <- mapM lblFromSym $ map _unAlphaOrd $ S.toList s
    return $ foldr joinLbl zeroLbl xs

normLabel :: Label -> Check Label
normLabel l = do
    l' <- simplLabel l
    s <- mkSymLbl l'
    lblFromSym' s



