{-# LANGUAGE FlexibleInstances, DeriveGeneric #-}
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

nameDefFlows :: NameExp -> NameType -> Sym SExp
nameDefFlows n nt = do
    sn <- symLbl (nameLbl n)
    case nt^.val of 
      NT_Enc t -> do
          l <- liftCheck $ coveringLabel' t
          sl <- symLbl l
          return (sFlows sl sn)
      NT_PKE t -> do
          l <- liftCheck $ coveringLabel' t
          sl <- symLbl l
          return (sFlows sl sn)
      NT_Sig t -> do
          l <- liftCheck $ coveringLabel' t
          sl <- symLbl l
          return (sFlows sl sn)
      NT_MAC t -> do
          l <- liftCheck $ coveringLabel' t
          sl <- symLbl l
          return (sFlows sl sn)
      NT_PRF xs -> do
          ys <- mapM (\(s, (a, nt)) -> nameDefFlows (prfName n s) nt) xs
          xs <- mapM (\p -> do
                x <- symLbl $ nameLbl $ prfName n $ fst p
                return $ sFlows x sn
                     ) xs
          return $ sAnd $ xs ++ ys 
      _ -> return sTrue


smtLabelSetup :: Sym ()
smtLabelSetup = do
    emitRaw "(declare-fun InLbl (LblBase Lbl) Bool)"
    emitRaw "(declare-fun Flows (Lbl Lbl) Bool)"
    emitRaw "(assert (forall ((x Lbl) (y Lbl)) (! (= (Flows x y) (forall ((b LblBase)) (=> (InLbl b x) (InLbl b y)) )) :pattern (Flows x y) )))"
    emitRaw "(declare-fun Join (Lbl Lbl) Lbl)"
    emitRaw "(assert (forall ((x Lbl) (y Lbl) (b LblBase)) (! (= (or (InLbl b x) (InLbl b y)) (InLbl b (Join x y)) ) :pattern (InLbl b (Join x y)) )))"
    emitRaw "(declare-fun %zeroLbl () Lbl)"
    emitRaw "(assert (forall ((b LblBase)) (! (not (InLbl b %zeroLbl)) :pattern (InLbl b %zeroLbl) )))"
    emitRaw "(assert (forall ((l Lbl)) (! (= (Flows l %zeroLbl) (= l %zeroLbl)) :pattern (Flows l %zeroLbl) )))"
    emit $ SApp [SAtom "declare-const", SAtom "%adv", SAtom "Lbl"]

    emitNameDefAssms
    x <- freshSMTName
    emitAssertion $ sForall [(SAtom x, nameSort)] (sNot $ sFlows (SApp [SAtom "LblOf", SAtom x]) (SAtom "%zeroLbl")) [(SApp [SAtom "LblOf", SAtom x])] 

    -- Flow axioms for abstract types
    fas <- liftCheck $ collectFlowAxioms
    forM_ fas $ \(l1, l2) -> do
        v1 <- symLbl l1
        v2 <- symLbl l2
        emitComment $ "Flow decl: " ++ show (pretty l1) ++ " <= " ++ show (pretty l2)
        emitAssertion $ sFlows v1 v2
    
    -- Constraints on the adv
    afcs <- liftCheck $ collectAdvCorrConstraints 
    forM_ afcs $ \(l1, l2) -> do
        v1 <- symLbl l1
        v2 <- symLbl l2
        ladv <- symLbl advLbl
        emitAssertion $ sImpl (sFlows v1 ladv) (sFlows v2 ladv)

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
                  emit $ SApp [SAtom "declare-const", SAtom x, SAtom "Lbl"]
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
        return $ SApp [SAtom "LblOf", n]
      CanonZero -> return $ SAtom "%zeroLbl"
      CanonAdv -> return $ SAtom "%adv"
      CanonConst s -> getSymLblConst s

getSymLblConst :: LblConst -> Sym SExp
getSymLblConst (TyLabelVar n@(PRes p)) = do
    e <- use symLabelVarEnv
    case M.lookup p e of
      Just res -> return res
      Nothing -> do
          let sname = SAtom $ "%lvar_" ++ (smtName p) 
          emit $ SApp [SAtom "declare-fun", sname, SApp [], SAtom "Lbl"]
          emitAssertion $ sFlows (SAtom "%adv") sname
          symLabelVarEnv %= (M.insert p sname)
          return sname


symLbl :: Label -> Sym SExp
symLbl l = do
    l' <- liftCheck $ simplLabel l
    c <- canonLabel l'
    symCanonLabel c

emitNameDefAssms :: Sym ()
emitNameDefAssms = do
    nE <- liftCheck $ collectNameEnv
    forM_ nE $ \(n, o) -> do 
        ((is1, is2), _) <- liftCheck $ unbind o
        ivs1 <- forM [1..length is1] $ \_ -> freshSMTIndexName
        ivs2 <- forM [1..length is2] $ \_ -> freshSMTIndexName
        sIE <- use symIndexEnv
        symIndexEnv  %= (M.union $ M.fromList $ map (\i -> (s2n i, SAtom i)) ivs1)
        symIndexEnv  %= (M.union $ M.fromList $ map (\i -> (s2n i, SAtom i)) ivs2)
        local (over (inScopeIndices) $ (++) $ map (\i -> (s2n i, IdxSession)) ivs1) $ 
            local (over (inScopeIndices)  $ (++) $ map (\i -> (s2n i, IdxPId)) ivs2) $ do
                let ne = mkSpanned $ BaseName (map (mkIVar . s2n) ivs1, map (mkIVar . s2n) ivs2) (PRes n)
                ntOpt <- liftCheck $ getNameTypeOpt ne
                assms <- case ntOpt of 
                    Just nt -> nameDefFlows ne nt
                    Nothing -> return sTrue
                emitAssertion $ sForall (map (\i -> (SAtom i, indexSort)) (ivs1 ++ ivs2)) assms []
        symIndexEnv .= sIE
    ros <- liftCheck $ collectRO
    forM_ ros $ \(s, (ae, nt)) -> do
        assm <- nameDefFlows (roName (PRes s)) nt
        emitAssertion assm





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



