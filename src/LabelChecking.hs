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
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import Data.List (sort)

instance Fresh Sym where
    fresh x = liftCheck $ fresh x


sFlows :: SExp -> SExp -> SExp
sFlows x y = SApp [SAtom "Flows", x, y]

sJoin :: SExp -> SExp -> SExp
sJoin x y = SApp [SAtom "Join", x, y]



nameDefFlows :: NameExp -> NameType -> Sym [(Label, Label)]
nameDefFlows n nt = do
    case nt^.val of 
      NT_Nonce -> return []
      NT_DH -> return []
      NT_Enc t -> do
          l <- liftCheck $ coveringLabel' t
          return $ [(l, mkSpanned $ LName n)]
      NT_StAEAD t _ _ _ -> do
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
        emitComment $ "Flow decl: " ++ show (owlpretty l1) ++ " <= " ++ show (owlpretty l2)
        emitAssertion $ sFlows v1 v2
    
    -- Constraints on the adv
    afcs <- liftCheck $ collectAdvCorrConstraints 
    ladv <- symLabel advLbl
    forM_ (zip afcs [0 .. (length afcs - 1)]) $ \(ils, j) -> do 
        ((is, xs), (l1, l2)) <- liftCheck $ unbind ils
        withIndices (map (\i -> (i, IdxGhost)) is) $ do
            withSMTVars xs $ do 
                v1 <- symLabel l1
                v2 <- symLabel l2
                emitAssertion $ sForall 
                    (map (\i -> (SAtom $ show i, indexSort)) is ++ map (\x -> (SAtom $ show x, bitstringSort)) xs)
                    (sImpl (sFlows v1 ladv) (sFlows v2 ladv))
                    []
                    ("advConstraint_" ++ show j)


getIdxVars :: Label -> [IdxVar]
getIdxVars l = toListOf fv l

-- Simplify the label, floating /\ above /\_i, removing /\_i if i is not used
simplLabel :: Label -> Check Label
simplLabel l = 
    case l^.val of
      LName _ -> return l
      LZero -> return l
      LAdv -> return l
      LTop -> return l
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
      LTop -> return $ CanonAnd [CanonNoBig $ CanonTop]
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
      LTop -> return (is, CanonTop)
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
                  emitComment $ "label for " ++ show (owlpretty c)
                  emit $ SApp [SAtom "declare-const", SAtom x, SAtom "Label"]
                  ivs <- mapM (\_ -> freshSMTIndexName) is
                  iEnv <- use symIndexEnv
                  forM_ ivs $ \iv -> 
                      symIndexEnv %= (M.insert (s2n iv) (SAtom iv))
                  lv <- symCanonAtom $ substs (zip is (map (mkIVar . s2n) ivs)) l
                  symIndexEnv .= iEnv
                  emitAssertion $ sForall (map (\i -> (SAtom i, indexSort)) ivs) (sFlows lv (SAtom x)) [] ("big_" ++ x)
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
      STop -> return topLbl
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



