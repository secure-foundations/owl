{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Typing where
import AST
import Data.Time.Clock
import qualified Data.Map.Strict as M
import Error.Diagnose.Position
import Data.Default (Default, def)
import qualified Data.Map.Ordered as OM
import qualified Data.Set as S
import CmdArgs
import Data.Maybe
import Data.Either
import Data.IORef
import Data.Ord
import System.FilePath (takeFileName, (</>))
import Control.Monad
import qualified Data.List as L
import qualified Data.List.Unique as UL
import Control.Monad.Reader
import qualified ANFPass as ANF
import qualified PathResolution as PR
import Control.Monad.Except
import Control.Monad.Cont
import Prettyprinter
import Prettyprinter.Render.Terminal
import Pretty
import Control.Lens
import LabelChecking
import TypingBase
import qualified Data.Map.Strict as M
import qualified SMT as SMT
import qualified SMTBase as SMT
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe
import qualified Error.Diagnose as E
import qualified Text.Parsec as P
import qualified System.IO as S
import qualified System.FilePath as S
import Parse
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

emptyModBody :: IsModuleType -> ModBody
emptyModBody t = ModBody t mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty 

-- extend with new parts of Env -- ok
emptyEnv :: Flags -> IO Env
emptyEnv f = do
    r <- newIORef 0
    r' <- newIORef 0
    r'' <- newIORef 0
    m <- newIORef $ M.empty
    rs <- newIORef []
    memo <- mkMemoEntry 
    return $ Env mempty mempty Nothing f initDetFuncs (TcGhost False) mempty [(Nothing, emptyModBody ModConcrete)] mempty 
        interpUserFunc r m [memo] mempty rs r' r'' (typeError') Nothing [] False def


assertEmptyParams :: [FuncParam] -> String -> Check ()
assertEmptyParams ps f =
    assert ("Function " ++ f ++ " does not expect params") $ length ps == 0

withNoParams :: String -> ([(AExpr, Ty)] -> Check TyX) -> [FuncParam] -> [(AExpr, Ty)] -> Check TyX
withNoParams f k ps args = do
    assertEmptyParams ps f
    k args


coveringLabelOf :: [Ty] -> Check Label
coveringLabelOf ts = do
    ls <- mapM coveringLabel ts
    return $ foldr joinLbl zeroLbl ls

trivialTypeOf :: [Ty] -> Check TyX
trivialTypeOf ts = do
    l <- coveringLabelOf ts
    return $ TData l l (ignore Nothing)

trivialTypeOfWithLength :: [Ty] -> AExpr -> Check TyX
trivialTypeOfWithLength ts ae = do
    t <- trivialTypeOf ts
    return $ TRefined (mkSpanned t) ".res" $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) ae

extractNameFromType :: Ty -> Maybe NameExp
extractNameFromType t =
    case (stripRefinements t)^.val of
      TName k -> Just k
      _ ->  Nothing

extractDHPKFromType :: Ty -> Maybe NameExp
extractDHPKFromType t =
    case (stripRefinements t)^.val of
      TDH_PK k -> Just k
      _ ->  Nothing

extractEncPKFromType :: Ty -> Maybe NameExp
extractEncPKFromType t =
    case (stripRefinements t)^.val of
      TEnc_PK k -> Just k
      _ ->  Nothing

extractVKFromType :: Ty -> Maybe NameExp
extractVKFromType t =
    case (stripRefinements t)^.val of
      TVK k -> Just k
      _ ->  Nothing

mkSimpleFunc :: String -> Int -> ([Ty] -> Check TyX) -> (String, (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX))
mkSimpleFunc s i k = (s, (i, withNoParams s (\args -> k (map snd args)))) 

withNormalizedTys :: Map String (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX)  ->
    Map String (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX)
withNormalizedTys mp =
    let f (x, y) = (x, \a b -> do
            b' <- mapM (\(a, t) -> do
                t' <- normalizeTy t
                return (a, t')) b
            y a b
            ) in
    map (\(k, v) -> (k, f v)) mp

mkRefined :: Ty -> (AExpr -> Prop) -> TyX              
mkRefined t p = TRefined t ".res" $ bind (s2n ".res") $ p $ aeVar ".res"

initDetFuncs :: Map String (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX)
initDetFuncs = withNormalizedTys $ [
    mkSimpleFunc "unit" 0 $ \args -> do
        return $ TUnit,
    mkSimpleFunc "true" 0 $ \args -> do
        return $ TBool zeroLbl,
    mkSimpleFunc "false" 0 $ \args -> do
        return $ TBool zeroLbl,
    ("eq", (2, \ps args -> do 
        assert ("Bad params") $ length ps == 0
        case args of
          [(a1, t1), (a2, t2)] -> do
              l1 <- coveringLabel t1
              l2 <- coveringLabel t2
              let true = aeApp (topLevelPath $ "true") [] []
              return $ mkRefined (mkSpanned $ TBool $ joinLbl l1 l2) $ \x ->
                    pImpl (pEq x true) (pEq a1 a2)
           )),
    ("Some", (1, \ps args -> do
        case (ps, args) of
          ([], [(x, t)]) -> do
              return $ TOption t
          ([ParamTy t], [(x, t1)]) -> do
              checkTy t
              b <- isSubtype t1 t
              l <- coveringLabel t1
              if b then return (TOption t) else return (TData l l $ ignore (Just $ "error on Some")) 
          _ -> typeError $ show $ ErrBadArgs "Some" (map snd args))),
    ("None", (0, \ps args -> do
        case (ps, args) of
          ([ParamTy t], []) -> do
              checkTy t
              return (TOption t)
          ([], []) -> do
              ot <- view expectedTy
              case ot of
                Nothing -> typeError $ "No option type inferrable from context"
                Just t -> do
                    case t^.val of
                      TOption _ -> return $ t^.val
                      _ -> typeError $ show $ owlpretty "Expected type is not option type: " <> owlpretty t
          _ -> typeError $ show $ ErrBadArgs "None" (map snd args))),
    ("andb", (2, \ps args -> do
        assert ("Bad params") $ length ps == 0
        case args of
          [(x, t1), (y, t2)] -> do
            l1 <- coveringLabel t1
            l2 <- coveringLabel t2
            let l = joinLbl l1 l2
            let tr = aeApp (topLevelPath $ "true") [] []
            assertSubtype t1 (mkSpanned $ TBool l)
            assertSubtype t2 (mkSpanned $ TBool l)
            return $ TRefined (mkSpanned $ TBool l) ".res" (bind (s2n ".res") $ pImpl (pEq (aeVar ".res") tr) (pAnd (pEq x tr) (pEq y tr)))
          _ -> typeError "Bad args for andb")),
    ("andp", (2, \ps args -> do
        assert ("Bad params") $ length ps == 0
        case args of
          [(_, Spanned _ (TRefined (Spanned _ TUnit) _ xp)), (_, Spanned _ (TRefined (Spanned _ TUnit) _ yp))] -> do 
              (x, p1) <- unbind xp
              (y, p2) <- unbind yp
              return $ TRefined (mkSpanned TUnit) "._" $ bind x $ pAnd p1 (subst y (aeVar' x) p2)
          _ -> typeError "Bad args for andp"
    )),
    ("notb", (1, \ps args -> do
        assert ("Bad params") $ length ps == 0
        case args of
          [(x, t)] -> do
              l <- coveringLabel t
              assertSubtype t (mkSpanned $ TBool l)
              let tr = aeApp (topLevelPath $ "true") [] []
              return $ TRefined (mkSpanned $ TBool l) ".res" $
                    bind (s2n ".res") $ mkSpanned $ pIff (pEq (aeVar ".res") tr) (pNot $ pEq x tr))),                      
    mkSimpleFunc "length" 1 $ \args -> do
        case args of
          [t] -> do
              l <- tyLenLbl t
              return $ TData l l (ignore Nothing)
          _ -> typeError $ show $ ErrBadArgs "length" args,
    mkSimpleFunc "plus" 2 $ \args -> trivialTypeOf args,
    mkSimpleFunc "crh" 1 $ \args -> trivialTypeOf args,
    mkSimpleFunc "mult" 2 $ \args -> trivialTypeOf args,
    mkSimpleFunc "zero" 0 $ \args -> trivialTypeOf args,
    mkSimpleFunc "is_group_elem" 1 $ \args -> do
        l <- coveringLabel $ head args
        return $ TBool l,
    mkSimpleFunc "concat" 2 $ \args -> trivialTypeOf args, -- Used for RO
    mkSimpleFunc "cipherlen" 1 $ \args -> trivialTypeOf args,
    mkSimpleFunc "pk_cipherlen" 1 $ \args -> trivialTypeOf args,
    mkSimpleFunc "vk" 1 $ \args ->
        case args of
          [t] | Just n <- extractNameFromType t -> do
              nt <- local (set tcScope (TcGhost False)) $ getNameType n
              case nt^.val of
                NT_Sig _ ->
                    return $ TRefined (mkSpanned $ TVK n) ".res" $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (mkSpanned $ AELenConst "vk")
                _ -> trivialTypeOf args
          _ -> trivialTypeOf args,
    mkSimpleFunc "dhpk" 1 $ \args ->
        case args of
          [t] | Just n <- extractNameFromType t -> do
              nt <- local (set tcScope (TcGhost False)) $ getNameType n
              case nt^.val of
                NT_DH -> return $ TDH_PK n
                _ -> trivialTypeOf args
          _ -> trivialTypeOf args,
    mkSimpleFunc "enc_pk" 1 $ \args ->
        case args of
          [t] | Just n <- extractNameFromType t -> do
              nt <-  local (set tcScope (TcGhost False)) $ getNameType n
              case nt^.val of
                NT_PKE _ -> return $ TEnc_PK n
                _ -> trivialTypeOf args
          _ -> trivialTypeOf args,
    ("dh_combine", (2, \ps args ->
        case (ps, args) of
          ([], [(_, t1), (_, t2)]) | Just n <- extractDHPKFromType t1, Just m <- extractNameFromType t2 -> do
              nt_n <-  local (set tcScope $ TcGhost False) $ getNameType n
              nt_m <-  local (set tcScope $ TcGhost False) $ getNameType m
              case (nt_n^.val, nt_m^.val) of
                (NT_DH, NT_DH) -> return $ TSS n m
                _ -> trivialTypeOf $ map snd args
          ([], _) -> trivialTypeOf $ map snd args
          ([ParamName n, ParamName m], [(x, t1), (_, t2)]) -> do 
              nt_n <-  local (set tcScope $ TcGhost False) $ getNameType n
              nt_m <-  local (set tcScope $ TcGhost False) $ getNameType m
              case (nt_n^.val, nt_m^.val) of
                (NT_DH, NT_DH) -> do
                  b1 <- isSubtype t1 (mkSpanned $ TDH_PK n)
                  b2 <- isSubtype t2 (tName m)
                  if b1 && b2 then return $ TSS n m else trivialTypeOf $ map snd args
                _ -> typeError $ "Wrong name types for dh_combine"
          _ -> typeError $ "Bad params to dh_combine: expected two name params"
                   )),
    ("checknonce", (2, \ps args ->
        case (ps, args) of
          ([], [(x, t1), (y, t2)]) ->
              case ((stripRefinements t1)^.val, (stripRefinements t2)^.val) of
                (TName n, TName m) -> do
                    l <- if n `aeq` m then return zeroLbl else (coveringLabelOf $ map snd args)
                    return $ TRefined (mkSpanned $ TBool l) ".res" $ bind (s2n ".res") $
                        pImpl (pEq (aeVar ".res") (aeApp (topLevelPath "true") [] []))
                              (pEq (mkSpanned $ AEGet n) (mkSpanned $ AEGet m))
                (TName n, m) -> do
                  nt <-  local (set tcScope $ TcGhost False) $ getNameType n
                  case nt^.val of
                    NT_Nonce -> do
                        l <- coveringLabel (mkSpanned m)
                        return $ TRefined (mkSpanned $ TBool l) ".res" (bind (s2n ".res") (pImpl (pEq (aeVar ".res") (aeApp (topLevelPath $ "true") [] [])) (pAnd (pFlow (nameLbl n) l) (pEq x y))))
                    _ -> trivialTypeOf $ map snd args
                (m, TName n) -> do
                  nt <-  local (set tcScope $ TcGhost False) $ getNameType n
                  case nt^.val of
                    NT_Nonce -> do
                        l <- coveringLabel (mkSpanned m)
                        return $ TRefined (mkSpanned $ TBool l) ".res" (bind (s2n ".res") (pImpl (pEq (aeVar ".res") (aeApp (topLevelPath $ "true") [] [])) (pAnd (pFlow (nameLbl n) l) (pEq x y))))
                    _ -> trivialTypeOf $ map snd args
                _ -> do
                  l <- coveringLabelOf $ map snd args
                  return $ TBool l
          _ -> typeError $ "Wrong parameters to checknonce"
    ))
    ]

mkStructType :: ResolvedPath -> TyVar -> [(AExpr, Ty)] -> [FuncParam] ->  Bind [IdxVar] (DepBind ()) -> Check TyX
mkStructType pth tv args ps b = do
    (is, dp) <- unbind b
    idxs <- getStructParams ps
    assert (show $ owlpretty "Wrong index arity for struct" <+> owlpretty pth <> owlpretty "." <> owlpretty (PRes $ PDot pth tv)) $ length idxs == length is
    let p = map (\(a, s) -> pEq a $ mkSpanned $ AEApp (PRes $ PDot pth s) ps [aeVar ".res"])
                (zip (map fst args) (depBindNames $ substs (zip is idxs) dp))
    return $ TRefined (mkSpanned $ TConst (PRes $ PDot pth tv) ps) ".res" $
        bind (s2n ".res") $ 
            pAnd (pEq (aeLength (aeVar ".res")) (sumOfLengths (map fst args)))
                 (foldr pAnd pTrue p)

tysMatchStructDef :: ResolvedPath -> TyVar -> [(AExpr, Ty)] -> [FuncParam] -> Bind [IdxVar] (DepBind ()) -> Check Bool
tysMatchStructDef pth sname args ps b = do
    (is, dp) <- unbind b
    idxs <- getStructParams ps
    assert (show $ owlpretty "Wrong index arity for struct" <+> owlpretty pth <> owlpretty "." <> owlpretty sname ) $ length idxs == length is
    go args $ substs (zip is idxs) dp
        where
            go [] (DPDone ()) = return True
            go ((a, t):args) (DPVar t1 sx xk) = do
                b1 <- isSubtype t t1 
                if b1 then do
                      (x, k) <- unbind xk
                      go args $ subst x a k
                else return False
            go _ _ = typeError "Bad number of arguments to tyMatchStructDef"


isGhost :: TcScope -> Bool
isGhost (TcGhost _) = True
isGhost (TcDef _) = False
        

interpUserFunc :: ResolvedPath -> ModBody -> UserFunc -> Check (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX)
interpUserFunc pth md (StructConstructor tv) = do
    case lookup tv (md^.tyDefs) of
      Just (StructDef idf) -> do
          let (is_ar, ar) = let (xs, ys) = unsafeUnbind idf in (length xs, length $ depBindNames ys)
          return (ar, \ps xs -> do
              forM_ ps checkParam
              assert (show $ owlpretty "Index arity mismatch on struct constructor") $ length ps == is_ar 
              if length xs == ar then do
                b <- tysMatchStructDef pth tv xs ps idf 
                if b then mkStructType pth tv xs ps idf else trivialTypeOf (map snd xs)
              else trivialTypeOf (map snd xs))
      _ -> typeError $ "Unknown struct: " ++ show tv
interpUserFunc pth md (StructProjector tv field) = do
    tc <- view tcScope  
    assert ("Struct accessors can only be called in ghost. Use a parse expression") $ isGhost tc
    case lookup tv (md^.tyDefs) of
      Just (StructDef idf) -> do
          let (is_ar, ar) = let (xs, ys) = unsafeUnbind idf in (length xs, length $ depBindNames ys)
          return (1, \ps args -> do
              forM_ ps checkParam
              assert (show $ owlpretty "Index arity mismatch on struct constructor") $ length ps == is_ar 
              nts <- extractStructTopDown ps (PRes $ PDot pth tv) (fst $ args !! 0) idf 
              case lookup field nts of
                Just t -> do
                  b <- isSubtype (snd $ args !! 0) (mkSpanned $ TConst (PRes $ PDot pth tv) ps)
                  if b then return (t^.val) else trivialTypeOf $ map snd args
                Nothing -> typeError $ "Unknown struct field: " ++ field)
      _ -> typeError $ "Unknown struct: " ++ show tv
interpUserFunc pth md (EnumConstructor tv variant) = do
    case lookup tv (md^.tyDefs) of
      Just (EnumDef idf) -> do
          let (is_ar, enum_map) = let (xs, ys) = unsafeUnbind idf in (length xs, ys)
          ar <- case lookup variant enum_map of
                  Nothing -> typeError $ "Unknown enum variant: " ++ variant
                  Just Nothing -> return 0
                  Just (Just _) -> return 1
          return (ar, \ps args -> do 
              forM_ ps checkParam
              nts <- extractEnum ps (show tv) idf
              assert (show $ owlpretty "Index arity mismatch on enum constructor") $ length ps == is_ar 
              let ot = fromJust $ lookup variant nts
              case ot of
                Nothing -> return $ TRefined (mkSpanned $ TConst (PRes $ PDot pth tv) (ps)) ".res" (bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (aeLenConst "tag"))
                Just t -> do
                    b <- isSubtype (snd $ args !! 0) t
                    if b then return (TRefined (mkSpanned $ TConst (PRes $ PDot pth tv) (ps)) ".res"
                                                          (bind (s2n ".res") $
                                                              pEq (aeLength (aeVar ".res"))
                                                                  (aeApp (topLevelPath $ "plus") [] [aeLength (fst $ args !! 0), aeLenConst "tag" ])))
                    else trivialTypeOf (map snd args))
      _ -> typeError $ "Unknown enum: " ++ show tv 
interpUserFunc pth md (EnumTest tv variant) = do
    return $ snd $ mkSimpleFunc (variant ++ "?") 1 $ \args ->
        case args of
          [t] -> 
              case (stripRefinements t)^.val of
                TConst s _ | s `aeq` (PRes $ PDot pth tv) -> return $ TBool advLbl
                _ -> do
                    l <- coveringLabel t
                    return $ TBool l
interpUserFunc pth md (FunDef b) = do
    let ar = length $ snd $ fst $ unsafeUnbind b
    return $ (ar, \ps as -> do
        t <- inferAExpr =<< extractFunDef b ps (map fst as)
        return $ t^.val)
interpUserFunc pth md (UninterpUserFunc f ar) = do
    return $ (ar, withNoParams (show f) $ \args -> do
        l <- coveringLabelOf $ map snd args
        return $ TRefined (tData l l) ".res" $ bind (s2n ".res") (pEq (aeVar ".res") (aeApp (PRes $ PDot pth f) [] (map fst args))))


normalizeProp :: Prop -> Check Prop
normalizeProp p = do
    p' <- go p
    if p `aeq` p' then return p' else normalizeProp p'
        where 
            go p = case p^.val of
                     PTrue -> return p
                     PFalse -> return p
                     PAnd (Spanned _ PTrue) p -> normalizeProp p
                     PAnd p (Spanned _ PTrue) -> normalizeProp p
                     PAnd (Spanned _ PFalse) p -> return pFalse
                     PAnd p (Spanned _ PFalse) -> return pFalse
                     PAnd p1 p2 -> do
                         p1' <- normalizeProp p1
                         p2' <- normalizeProp p2
                         if p1' `aeq` p2' then return p1' else
                             return $ Spanned (p^.spanOf) $ PAnd p1' p2'
                     POr (Spanned _ PTrue) p -> return pTrue
                     POr p (Spanned _ PTrue) -> return pTrue
                     POr (Spanned _ PFalse) p -> normalizeProp p
                     POr p (Spanned _ PFalse) -> normalizeProp p
                     POr p1 p2 -> do
                         p1' <- normalizeProp p1
                         p2' <- normalizeProp p2
                         if p1' `aeq` p2' then return p1' else
                             return $ Spanned (p^.spanOf) $ POr p1' p2'
                     PImpl (Spanned _ PTrue) p -> normalizeProp p
                     PImpl _ (Spanned _ PTrue) -> return pTrue  
                     PImpl (Spanned _ PFalse) p -> return pTrue
                     PImpl p (Spanned _ PFalse) -> pNot <$> normalizeProp p
                     PImpl p1 p2 -> do 
                         p1' <- normalizeProp p1
                         p2' <- normalizeProp p2
                         return $ Spanned (p^.spanOf) $ PImpl p1' p2'
                     PEq a1 a2 -> do
                         a1' <- resolveANF a1 >>= normalizeAExpr 
                         a2' <- resolveANF a2 >>= normalizeAExpr 
                         return $ Spanned (p^.spanOf) $ PEq a1' a2'
                     PLetIn a xp -> do
                         (x, p) <- unbind xp
                         normalizeProp $ subst x a p
                     PNot (Spanned _ PTrue) -> return pFalse
                     PNot (Spanned _ PFalse) -> return pTrue
                     PNot p1 -> do
                         p' <- normalizeProp p1
                         return $ Spanned (p^.spanOf) $ PNot p'
                     PQuantBV q sx xp -> do
                         (x, p') <- unbind xp
                         case p'^.val of
                           PAnd p1' p2' -> normalizeProp $ Spanned (p^.spanOf) $ 
                                            PAnd 
                                                (mkSpanned $ PQuantBV q sx $ bind x p1') 
                                                (mkSpanned $ PQuantBV q sx $ bind x p2') 
                           _ -> do 
                             p2' <- withVars [(x, (ignore $ show x, Nothing, tGhost))] $ normalizeProp p'
                             return $ if x `elem` toListOf fv p2' then (Spanned (p^.spanOf) $ PQuantBV q sx (bind x p2')) else p2'
                     PQuantIdx q sx xp -> do
                         (x, p') <- unbind xp
                         case p'^.val of
                           PAnd p1' p2' -> normalizeProp $ Spanned (p^.spanOf) $ 
                                            PAnd 
                                                (mkSpanned $ PQuantIdx q sx $ bind x p1') 
                                                (mkSpanned $ PQuantIdx q sx $ bind x p2') 
                           _ -> do 
                             p2' <- withIndices [(x, IdxGhost)] $ normalizeProp p'
                             return $ if x `elem` toListOf fv p2' then (Spanned (p^.spanOf) $ PQuantIdx q sx (bind x p2')) else p2'
                     PFlow a b -> do
                         a' <- normLabel a
                         b' <- normLabel b
                         if a' `aeq` b' then return pTrue else return (Spanned (p^.spanOf) $ PFlow a' b')
                     _ -> return p


-- Normalize a type expression. Only nontrivial computations are to normalize a
-- nested refinement, and to normalize a case whether a name n is honest.
normalizeTy :: Ty -> Check Ty
normalizeTy = withMemoize (memoNormalizeTy) $ \t0 -> 
    withSpan (t0^.spanOf) $ local (set tcScope $ TcGhost False) $ do
        case t0^.val of
            TUnit -> return tUnit
            (TCase p t1 t2) -> 
                if t1 `aeq` t2 then normalizeTy t1 else do
                    ob <- decideProp p
                    t1' <- normalizeTy t1
                    t2' <- normalizeTy t2
                    case ob of
                      Nothing -> do
                          b1 <- isSubtype t1 t2
                          b2 <- isSubtype t2 t1
                          if (b1 && b2) then return t1' else return $ Spanned (t0^.spanOf) $ TCase p t1' t2'
                      Just b -> return $ if b then t1' else t2'
            (TOption t) -> do
                t' <- normalizeTy t
                return $ Spanned (t0^.spanOf) $ TOption t'
            (TRefined (Spanned _ (TRefined t s1 xp1)) s2 yp2) -> do  -- x:(y:t{p1}){p2} --> x:t{p1 /\ p2}
                (x, p1) <- unbind xp1
                (y, p2) <- unbind yp2
                normalizeTy $ Spanned (t0^.spanOf) $ TRefined t s2 $ bind y $ pAnd (subst x (mkSpanned $ AEVar (ignore s2) y) p1) p2 
            (TRefined t s xp) -> do
                t' <- normalizeTy t
                (x, p) <- unbind xp
                p' <- withVars [(x, (ignore $ show x, Nothing, t'))] $ normalizeProp p
                return $ Spanned (t0^.spanOf) $ TRefined t' s $ bind x p'
            (TUnion t1 t2) -> do
                t1' <- normalizeTy t1
                t2' <- normalizeTy t2
                return $ Spanned (t0^.spanOf) $ TUnion t1' t2'
            (TData l1 l2 s) -> do
                l1' <- normalizeLabel l1
                l2' <- normalizeLabel l2
                return $ Spanned (t0^.spanOf) $ TData l1' l2' s
            (TDataWithLength l a) -> do
                l' <- normalizeLabel l
                return $ Spanned (t0^.spanOf) $ TDataWithLength l' a
            (TBool l) -> do
                l' <- normalizeLabel l
                return $ Spanned (t0^.spanOf) $ TBool l'
            TGhost -> return t0
            (TName n) -> do
                n' <- normalizeNameExp n
                return $ Spanned (t0^.spanOf) $ TName n'
            (TVK n) -> do
                n' <- normalizeNameExp n
                return $ Spanned (t0^.spanOf) $ TVK n'
            (TDH_PK n) -> do
                n' <- normalizeNameExp n
                return $ Spanned (t0^.spanOf) $ TDH_PK n'
            (TEnc_PK n) -> do
                n' <- normalizeNameExp n
                return $ Spanned (t0^.spanOf) $ TEnc_PK n'
            (TSS n m) -> do
                n' <- normalizeNameExp n
                m' <- normalizeNameExp m
                return $ Spanned (t0^.spanOf) $ TSS n' m'
            TConst s ps -> do
                td <- getTyDef s
                case td of
                  TyAbstract -> return t0
                  TyAbbrev t -> normalizeTy t
                  StructDef _ -> return t0
                  EnumDef _ ->
                      case ps of
                        ps' -> do
                            return $ Spanned (t0^.spanOf) $ TConst s (ps')
            (TExistsIdx xt) -> do
                (x, t) <- unbind xt
                if x `elem` getTyIdxVars t then do
                    t' <- withIndices [(x, IdxGhost)] $ normalizeTy t
                    return $ Spanned (t0^.spanOf) $ TExistsIdx $ bind x t'
                else normalizeTy t
            TAdmit -> return t0
            THexConst a -> return t0

normalizeLabel :: Label -> Check Label
normalizeLabel l = do                
    normLabel l



-- Subtype checking, assuming the types are normalized

isSubtype' t1 t2 = do
    case (t1^.val, t2^.val) of
      (_, TGhost) -> return True
      _ | isSingleton t2 -> do 
          (_, b) <- SMT.smtTypingQuery "singleton check" $ SMT.subTypeCheck t1 t2
          return b 
      (TCase p t1' t2', _) -> do
          r <- decideProp p
          case r of
            Just b -> isSubtype' (if b then t1' else t2') t2
            Nothing -> do
              b1 <- isSubtype' t1' t2
              b2 <- isSubtype' t2' t2
              return $ b1 && b2
      (_, TCase p t1' t2') -> do
          r <- decideProp p
          case r of
            Just b -> isSubtype' t1 (if b then t1' else t2')
            Nothing -> do
              b1 <- isSubtype' t1 t1'
              b2 <- isSubtype' t1 t2'
              return $ b1 && b2
      (TAdmit, _) -> return True
      (t1', t2') | t1' `aeq` t2' -> return True
      (TOption t1, TOption t2) -> isSubtype' t1 t2
      (_, TRefined t _ p) -> do
          b1 <- isSubtype' t1 t
          (_, b2) <- SMT.smtTypingQuery "refinement check" $ SMT.subTypeCheck t1 t2
          return $ b1 && b2
      (TRefined t _ _, t') | (t^.val) `aeq` t' -> return True
      (_, TUnit) -> snd <$> (SMT.smtTypingQuery "unit check" $ SMT.subTypeCheck t1 t2)
      (TUnit,  _) -> do
        isSubtype' (tRefined (tData zeroLbl zeroLbl) "_x" $ (pEq (aeVar "_x") (aeApp (topLevelPath $ "unit") [] []))) t2
      (TBool l1, TBool l2) -> do
          ob <- tryFlowsTo l1 l2
          case ob of
            Nothing -> return False
            Just b -> return b
      (TConst x ps1, TConst y ps2) -> do
          x' <- normalizePath x
          y' <- normalizePath y
          td <- getTyDef x
          case (aeq x' y', td) of
            (True, EnumDef _) -> return $ aeq ps1 ps2 
            (True, StructDef _) -> do
                assert (show $ owlpretty "Func param arity mismatch on struct") $ length ps1 == length ps2
                qs <- forM (zip ps1 ps2) $ \(p1, p2) ->
                    case (p1, p2) of
                      (ParamIdx i1 _, ParamIdx i2 _) -> return $ mkSpanned $ PEqIdx i1 i2
                      _ -> typeError $ "Bad param to struct: didn't get index"
                let p = foldr pAnd pTrue qs
                (_, b) <- SMT.smtTypingQuery "index equality check" $ SMT.symAssert p
                return b
            _ -> return False
      (TSS n m, TSS m' n') | (n `aeq` n') && (m `aeq` m') -> return True -- TODO maybe all we want? not sure
      (TExistsIdx xt1, TExistsIdx xt2) -> do
          (xi, t1) <- unbind xt1
          (xi', t2) <- unbind xt2
          withIndices [(xi, IdxGhost)] $ 
              isSubtype' t1 (subst xi' (mkIVar xi) t2)
      (_, TUnion t1' t2') -> do
          b1 <- isSubtype' t1 t1'
          b2 <- isSubtype' t1 t2'
          return $ b1 || b2
      (t, TDataWithLength l a) -> do
          b1 <- isSubtype' t1 (tData l l)
          (_, b) <- SMT.smtTypingQuery "TDataWithLength check" $ SMT.subTypeCheck t1 t2
          return $ b1 && b
      (t, TData l1 l2 _) -> do
        l2' <- tyLenLbl t1
        b1 <- tyFlowsTo t1 l1 
        ob2 <- tryFlowsTo l2' l2
        case ob2 of
          Nothing -> return False
          Just b2 -> return $ b1 && b2
      (TRefined t _ _, _) -> isSubtype' t t2
      _ -> return False

isSingleton :: Ty -> Bool
isSingleton t = 
    case t^.val of
      TName _ -> True
      TVK _ -> True
      TDH_PK _ -> True
      TEnc_PK _ -> True
      TSS _ _ -> True
      THexConst _ -> True
      _ -> False

tyFlowsTo :: Ty -> Label -> Check Bool
tyFlowsTo t l = 
    case t^.val of
      TSS n m -> do
          ob1 <- tryFlowsTo (joinLbl (nameLbl n) advLbl) l
          ob2 <- tryFlowsTo (joinLbl (nameLbl m) advLbl) l
          return $ (ob1 == Just True) || (ob2 == Just True)
      _ -> do
          l1 <- coveringLabel t
          ob <- tryFlowsTo l1 l
          return $ ob == Just True

-- We check t1 <: t2  by first normalizing both
isSubtype :: Ty -> Ty -> Check Bool
isSubtype t1 t2 = do
    t1' <- normalizeTy t1
    t2' <- normalizeTy t2
    b <- isSubtype' t1' t2'
    return b



assertSubtype :: Ty -> Ty -> Check ()
assertSubtype t1 t2 = laxAssertion $ do
    tyc <- view tyContext
    b <- isSubtype t1 t2
    t1' <- normalizeTy t1
    t2' <- normalizeTy t2
    assert (show $ ErrCannotProveSubtype t1' t2') b


coveringLabel :: Ty -> Check Label
coveringLabel t = local (set tcScope $ TcGhost False) $ do
    t' <- normalizeTy t
    coveringLabel' t'


addDef :: String -> Def -> Check a -> Check a
addDef n df cont = do
    dfs <- view $ curMod . defs
    case (df, lookup n dfs) of
      (_, Nothing) -> local (over (curMod . defs) $ insert n df) $ cont
      (DefHeader _, Just _) -> typeError $ "Def already defined: " ++ n
      (Def isdp, Just (DefHeader bl)) -> do
          (is, DefSpec _ l _) <- unbind isdp
          assert ("Locality mismatch for " ++ n) $ (bind is l) `aeq` bl 
          local (over (curMod . defs) $ insert n df) $ cont
      (Def isdp, Just (Def isdp')) -> do
          (is, DefSpec abs1 l1 ret1) <- unbind isdp
          (_, DefSpec abs2 _ _) <- unbind isdp'
          assert ("Duplicate abstract def: " ++ n) $ not (unignore abs1) 
          assert ("Def already defined: " ++ n) $ unignore abs2
          defMatches n (Just $ Def isdp) (Def isdp') 
          local (over (curMod . defs) $ insert n df) $ cont


addTyDef :: TyVar -> TyDef -> Check a -> Check a
addTyDef s td k = do
    tds <- view $ curMod . tyDefs
    case lookup s tds of
      Nothing -> local (over (curMod . tyDefs) $ insert s td) k 
      Just TyAbstract -> do
          -- Check if length label of td flows to adv
          len_lbl <- case td of
            EnumDef bts -> typeError $ show $ owlpretty "Cannot assign abstract type " <> owlpretty s <> owlpretty " to enum def "
            StructDef sd -> do
                (is, xs') <- unbind sd
                assert (show $ owlpretty "Cannot assign abstract type " <> owlpretty s <> owlpretty " to indexed struct") $ length is == 0
                error "TODO: abstract ty for structs"
            TyAbbrev t -> tyLenLbl t
            TyAbstract -> typeError $ show $ owlpretty "Overlapping abstract types: " <> owlpretty s
          len_lbl' <- tyLenLbl $ mkSpanned $ TConst (topLevelPath s) []
          local (over (curMod . flowAxioms) $ \xs -> (len_lbl, len_lbl') : (len_lbl', len_lbl) : xs ) $
              local (over (curMod . tyDefs) $ insert s td) $
                  k
      Just _ -> typeError $ show $ owlpretty "Type already defined: " <> owlpretty s

addNameDef :: String -> ([IdxVar], [IdxVar]) -> (NameType, [Locality]) -> Check a -> Check a
addNameDef n (is1, is2) (nt, nls) k = do
    md <- view curMod
    _ <- case lookup n (md ^. nameDefs) of
      Nothing -> return ()
      Just o -> do
        ((is1', is2'), nd) <- unbind o
        case nd of
          AbstractName -> do
              withSpan (nt^.spanOf) $ assert (show $ owlpretty "Indices on abstract and concrete def of name" <+> owlpretty n <+> owlpretty "do not match") $ (length is1 == length is1' && length is2 == length is2')
          _ -> typeError $ "Duplicate name: " ++ n
    withSpan (nt^.spanOf) $ assert (show $ owlpretty "Duplicate indices in definition: " <> owlpretty (is1 ++ is2)) $ UL.allUnique (is1 ++ is2)
    withIndices (map (\i -> (i, IdxSession)) is1 ++ map (\i -> (i, IdxPId)) is2) $ do
            forM_ nls normLocality
            checkNameType nt
    local (over (curMod . nameDefs) $ insert n (bind (is1, is2) (BaseDef (nt, nls)))) $ k

addNameAbbrev :: String ->  ([IdxVar], [IdxVar]) -> (Bind [DataVar] NameExp) -> Check a -> Check a
addNameAbbrev n (is1, is2) bne k = do
    md <- view curMod
    case lookup n (md^.nameDefs) of
      Nothing -> return ()
      Just o -> do
        ((is1', is2'), nd) <- unbind o
        case nd of
          AbstractName -> do
              assert (show $ owlpretty "Indices on abstract and concrete def of name" <+> owlpretty n <+> owlpretty "do not match") $ (length is1 == length is1' && length is2 == length is2')
          _ -> typeError $ "Duplicate name: " ++ n
    assert (show $ owlpretty "Duplicate indices in definition: " <> owlpretty (is1 ++ is2)) $ UL.allUnique (is1 ++ is2)
    withIndices (map (\i -> (i, IdxSession)) is1 ++ map (\i -> (i, IdxPId)) is2) $ do
        (xs, ne) <- unbind bne
        withVars (map (\x -> (x, (ignore $ show x, Nothing, tGhost))) xs) $ do
            _ <- getNameInfo ne
            return ()
    local (over (curMod . nameDefs) $ insert n (bind (is1, is2) (AbbrevNameDef bne))) $ k


sumOfLengths :: [AExpr] -> AExpr
sumOfLengths [] = aeApp (topLevelPath $ "zero") [] []
sumOfLengths (x:xs) = aeApp (topLevelPath $ "plus") [] [aeLength x, sumOfLengths xs]

inferModuleExp :: ModuleExp -> Check ModDef
inferModuleExp me = 
    case me^.val of
      ModuleBody imt xds' -> do
          (x, ds') <- unbind xds'
          m' <- local (over openModules $ insert (Just x) (emptyModBody imt)) $ checkDeclsWithCont ds' $ view curMod
          let md = MBody $ bind x m'
          return md
      ModuleFun xe -> do
          ((x, s, t), k) <- unbind xe
          p <- curModName
          t1 <- inferModuleExp $ unembed t 
          kind_t1 <- modDefKind t1
          withSpan (me^.spanOf) $ assert (show $ owlpretty "Not a module type: " <> owlpretty (unembed t)) $ kind_t1 == ModType
          t1Concrete <- makeModDefConcrete t1
          r <- local (over modContext $ insert x t1Concrete) $ 
                  inferModuleExp k
          return $ MFun s t1 (bind x r)
      ModuleApp e1 arg@(PRes argp) -> do
          md <- inferModuleExp e1 
          case md of
            MBody _ -> typeError $ "Not a functor: " ++ show e1
            MFun _ s xd -> do
              argd <- getModDef argp
              kind_argd <- modDefKind argd
              withSpan (me^.spanOf) $ assert ("Not a module: " ++ show argp) $ kind_argd == ModConcrete
              moduleMatches argd s 
              (x, d) <- unbind xd
              return $ subst x argp d
      ModuleVar pth@(PRes (PDot p s)) -> do
          md1 <- openModule p
          case lookup s (md1^.modules) of 
            Just b -> return b
            Nothing -> typeError $ "Unknown module or functor: " ++ show pth
      ModuleVar pth@(PRes (PPathVar OpenPathVar x)) -> do
          cm <- view openModules
          case lookup (Just x) cm of
              Just md -> return $ MBody $ bind x md
              Nothing -> typeError $ "Unknown module or functor: " ++ show pth
      ModuleVar pth@(PRes (PPathVar (ClosedPathVar _) x)) -> do
          mc <- view modContext
          case lookup x mc of
            Just b -> return b
            Nothing ->  typeError $ "Unknown module or functor: " ++ show pth
      _ -> error $ "Unknown case: " ++ show me

singleLineSpan :: Ignore Position -> Ignore Position
singleLineSpan i = 
    ignore $ go $ unignore i
        where
            go (Position b e i) = Position b (f b) i
            f b = (fst b, 100)

ensureNoConcreteDefs :: Check ()
ensureNoConcreteDefs = do
    dfs <- view $ curMod . defs
    forM_ dfs $ \(_, d) -> do
        case d of
          DefHeader _ -> return ()
          Def ds -> do
              let (_, d) = unsafeUnbind ds 
              assert ("Decl cannot appear after concrete def") $ unignore $ _isAbstract d


withDepBind :: (Alpha a, Alpha b) => DepBind a -> ([(DataVar, String, Ty)] -> a -> Check b) -> Check (DepBind b)
withDepBind (DPDone x) k = DPDone <$> k [] x
withDepBind (DPVar t s xd) k = do
    (x, d) <- unbind xd
    res <- withVars [(x, (ignore $ show x, Nothing, t))] $ withDepBind d $ \args v -> k ((x, s, t):args) v
    return $ DPVar t s (bind x res)
                                          
unsafeMapDepBind :: Alpha a => DepBind a -> (a -> b) -> b
unsafeMapDepBind (DPDone x) k = k x
unsafeMapDepBind (DPVar _ _ xd) k = 
    let (x, d) = unsafeUnbind xd in
    unsafeMapDepBind d k
                  
checkDecl :: Decl -> Check a -> Check a
checkDecl d cont = withSpan (d^.spanOf) $ 
    case d^.val of
      (DeclLocality n dcl) -> do
          ensureNoConcreteDefs
          case dcl of
            Left i -> local (over (curMod . localities) $ insert n (Left i)) $ cont
            Right (PRes pth@(PDot p s)) -> do
                md <- openModule p
                case lookup s (md^.localities) of 
                  Nothing -> typeError $ "Unknown locality: " ++ show pth
                  Just _ -> local (over (curMod . localities) $ insert n (Right pth)) $ cont
      DeclInclude _ -> error "Include found during type inference"
      DeclCounter n isloc -> do
          ensureNoConcreteDefs
          ((is1, is2), loc) <- unbind isloc
          withIndices (map (\i -> (i, IdxSession)) is1 ++ map (\i -> (i, IdxPId)) is2) $ do
              normLocality loc
          local (over (curMod . ctrEnv) $ insert n (bind (is1, is2) loc)) $ cont
      DeclSMTOption s1 s2 -> do
        local (over z3Options $ M.insert s1 s2) $ cont
      DeclFun s bnd -> do
          ufs <- view $ curMod . userFuncs
          assert ("Duplicate function: " ++ show s) $ not $ member s ufs
          (((is, ps), xs), a) <- unbind bnd
          withIndices (map (\i -> (i, IdxSession)) is ++ map (\i -> (i, IdxPId)) ps) $ do
              withVars (map (\x -> (x, (ignore $ show x, Nothing, tGhost))) xs) $ do
                  _ <- inferAExpr a
                  return ()
          local (over (curMod . userFuncs) $ insert s (FunDef bnd)) $ cont
      DeclPredicate s bnd -> do 
        preds <- view $ curMod . predicates
        assert ("Duplicate predicate: " ++ show s) $ not $ member s preds
        ((is, xs), p) <- unbind bnd
        local (set tcScope $ TcGhost False) $ do
            withIndices (map (\i -> (i, IdxGhost)) is) $ do
                withVars (map (\x -> (x, (ignore $ show x, Nothing, tGhost))) xs) $ do
                    checkProp p
        local (over (curMod . predicates) $ insert s bnd) $ cont
      DeclName n o -> do
        ensureNoConcreteDefs
        ((is1, is2), ndecl) <- unbind o
        case ndecl of 
          DeclAbstractName -> local (over (curMod . nameDefs) $ insert n (bind (is1, is2) AbstractName)) $ cont
          DeclBaseName nt nls -> addNameDef n (is1, is2) (nt, nls) $ cont
          DeclAbbrev bne -> addNameAbbrev n (is1, is2) bne $ cont
      DeclModule n imt me omt -> do
          ensureNoConcreteDefs
          md <- case me^.val of
                  ModuleVar (PRes p) -> return $ MAlias p 
                  _ -> inferModuleExp me
          kind_md <- modDefKind md
          case imt of
            ModConcrete -> assert ("Expected module, got module type: " ++ show (owlpretty me)) $ kind_md == imt
            ModType -> assert ("Expected module type, got module: " ++ show (owlpretty me)) $ kind_md == imt
          case omt of
            Nothing -> return ()
            Just mt -> do
              mdt <- inferModuleExp mt
              kind_mdt <- modDefKind mdt
              assert ("Expected module type: " ++ show (owlpretty mt)) $ kind_mdt == ModType
              withSpan (singleLineSpan $ d^.spanOf) $ moduleMatches md mdt 
          local (over (curMod . modules) $ insert n md) $ cont
      DeclDefHeader n isl -> do
          ((is1, is2), l) <- unbind isl
          withIndices (map (\i -> (i, IdxSession)) is1 ++ map (\i -> (i, IdxPId)) is2) $ do
              normLocality l
          let df = DefHeader isl 
          addDef n df $ cont
      DeclDef n o1 -> do
          ((is1, is2), (l, db)) <- unbind o1
          dspec <- withIndices (map (\i -> (i, IdxSession)) is1 ++ map (\i -> (i, IdxPId)) is2) $ do
                  normLocality l
                  withDepBind db $ \args (opreReq, tyAnn, bdy) -> do   
                      forM_ args $ \(_, _, t) -> checkTy t
                      let preReq = case opreReq of
                             Nothing -> pTrue
                             Just p -> p
                      checkProp preReq
                      checkTy tyAnn
                      let happenedProp = pHappened (topLevelPath n) (map mkIVar is1, map mkIVar is2) (map aeVar' $ map (\(x, _, _) -> x) args)
                      x <- freshVar
                      case bdy of
                        Nothing -> return $ (preReq, tyAnn, Nothing)
                        Just bdy' -> do
                          onlyCheck <- view $ envFlags . fOnlyCheck
                          let doCheck = (onlyCheck == Nothing) || (onlyCheck == Just n)
                          when doCheck $ do 
                              bdy'' <- ANF.anf bdy'
                              logTypecheck $ owlpretty $ "Type checking " ++ n
                              t0 <- liftIO $ getCurrentTime
                              pushLogTypecheckScope
                              local (set tcScope $ TcDef l) $ local (set curDef $ Just n) $ 
                                  withVars [(s2n x, (ignore x, Nothing, mkSpanned $ TRefined tUnit ".req" (bind (s2n ".req") (pAnd preReq happenedProp))))] $ do
                                  _ <- checkExpr (Just tyAnn) bdy''
                                  popLogTypecheckScope
                                  t1 <- liftIO $ getCurrentTime
                                  logTypecheck $ owlpretty $ "Finished checking " ++ n ++ " in " ++ show (diffUTCTime t1 t0)
                          return $ (preReq, tyAnn, Just bdy')
          let is_abs = ignore $ unsafeMapDepBind dspec $ \(_, _, o) -> not $ isJust o
          let df = Def $ bind (is1, is2) $ DefSpec is_abs l dspec
          addDef n df $ cont
      (DeclCorr ils) -> do
          ensureNoConcreteDefs
          ((is, xs), (l1, l2)) <- unbind ils
          withIndices (map (\i -> (i, IdxGhost)) is) $ do
            withVars (map (\x -> (x, (ignore $ show x, Nothing, tGhost))) xs) $ do
              checkLabel l1
              checkLabel l2
          let cc = bind (is, xs) $ CorrImpl l1 l2
          local (over (curMod . advCorrConstraints) $ \xs -> cc : xs ) $ cont
      (DeclCorrGroup ils) -> do
          ensureNoConcreteDefs
          ((is, xs), ls) <- unbind ils
          withIndices (map (\i -> (i, IdxGhost)) is) $ do
            withVars (map (\x -> (x, (ignore $ show x, Nothing, tGhost))) xs) $ do
              mapM_ checkLabel ls
          let cc = bind (is, xs) $ CorrGroup ls
          local (over (curMod . advCorrConstraints) $ \xs -> cc : xs ) $ cont
      (DeclStruct n ixs) -> do
          logTypecheck $ owlpretty $ "Checking struct: " ++ n
          (is, xs) <- unbind ixs
          dfs <- view detFuncs
          tvars <- view $ curMod . tyDefs
          assert (show $ owlpretty n <+> owlpretty "already defined") $ not $ member n tvars
          assert (show $ owlpretty n <+> owlpretty "already defined") $ not $ member n dfs
          assert (show $ owlpretty "Duplicate constructor / destructor") $ uniq $ n : depBindNames xs
          snames_ <- withIndices (map (\i -> (i, IdxGhost)) is) $ do
              withDepBind xs $ \args _ -> do 
                  snames <- forM args $ \(x, s, t) -> do 
                      checkTy t
                      assert (show $ owlpretty s <+> owlpretty "already defined") $ not $ member s dfs
                      case (stripRefinements t)^.val of
                        TGhost -> return ()
                        _ -> do
                          llbl <- tyLenLbl t
                          flowCheck llbl advLbl
                      return s
                  return snames
          let snames = unsafeMapDepBind snames_ id 
          let projs = map (\s -> (s, StructProjector n s)) snames 
          local (over (curMod . userFuncs) $ insert n (StructConstructor n)) $ 
              local (over (curMod . userFuncs) $ mappend projs) $ 
                  addTyDef n (StructDef ixs) $ 
                      cont
      (DeclEnum n b) -> do
        (is, bdy) <- unbind b
        withIndices (map (\i -> (i, IdxGhost)) is) $ do
            mapM_ checkTy $ catMaybes $ map snd bdy
        assert ("Enum cases must be unique") $ uniq $ map fst bdy
        assert (show $ "Enum " ++ n ++ " must be nonempty") $ length bdy > 0
        let constrs = map (\(x, ot) -> (x, EnumConstructor n x)) bdy 
        let tests = map (\(x, ot) -> (x ++ "?", EnumTest n x)) bdy
        local (over (curMod . userFuncs) $ mappend (constrs ++ tests)) $ 
            addTyDef n (EnumDef b) $
                cont
      DeclNameType s bnt -> do
          tds <- view $ curMod . nameTypeDefs
          assert ("Duplicate name type name: " ++ s) $ not $ member s tds
          ((is, ps), nt) <- unbind bnt
          withIndices (map (\i -> (i, IdxSession)) is ++ map (\i -> (i, IdxPId)) ps) $ do 
                checkNameType nt
          local (over (curMod . nameTypeDefs) $ insert s bnt) $ cont
      DeclODH s b -> do
          ensureNoConcreteDefs
          ((is, ps), (ne1, ne2, kdf)) <- unbind b
          withIndices (map (\i -> (i, IdxSession)) is ++ map (\i -> (i, IdxPId)) ps) $ do 
                nt <- getNameType ne1
                nt2 <- getNameType ne2
                assert ("Name " ++ show (owlpretty ne1) ++ " must be DH") $ nt `aeq` (mkSpanned $ NT_DH)
                assert ("Name " ++ show (owlpretty ne1) ++ " must be DH") $ nt2 `aeq` (mkSpanned $ NT_DH)
                b1 <- nameExpIsLocal ne1
                b2 <- nameExpIsLocal ne2

                assert ("Name must be local to module: " ++ show (owlpretty ne1)) $ b1
                assert ("Name must be local to module: " ++ show (owlpretty ne2)) $ b2
                let indsLocal = all (\i -> i `elem` (toListOf fv ne1 ++ toListOf fv ne2)) (is ++ ps)
                assert ("All indices in odh must appear in name expressions") indsLocal
                checkNameType $ mkSpanned $ NT_KDF KDF_IKMPos kdf
          ensureODHDisjoint (bind (is, ps) (ne1, ne2))
          local (over (curMod . odh) $ insert s b) $ cont
      (DeclTy s ot) -> do
        tds <- view $ curMod . tyDefs
        case ot of
          Just t -> do
            checkTy t
            addTyDef s (TyAbbrev t) cont
          Nothing ->
            local (over (curMod . tyDefs) $ insert s (TyAbstract)) $
                    cont
      (DeclTable n t loc) -> do
          ensureNoConcreteDefs
          tbls <- view $ curMod . tableEnv
          locs <- view $ curMod . localities
          assert (show $ owlpretty "Duplicate table name: " <> owlpretty n) (not $ member n tbls)
          normLocality loc
          checkTy t
          local (over (curMod . tableEnv) $ insert n (t, loc)) cont
      (DeclDetFunc f opts ar) -> do
        dfs <- view detFuncs
        assert (show $ owlpretty f <+> owlpretty "already defined") $ not $ member f dfs
        local (over (curMod . userFuncs) $ insert f (UninterpUserFunc f ar)) $ 
            cont

ensureODHDisjoint :: Bind ([IdxVar], [IdxVar]) (NameExp, NameExp) -> Check ()
ensureODHDisjoint b = do
    cur_odh <- view $ curMod . odh
    ((is, ps), (ne1, ne2)) <- unbind b
    withIndices (map (\i -> (i, IdxSession)) is ++ map (\i -> (i, IdxPId)) ps) $ do
            forM_ cur_odh $ \(_, bnd2) -> do
                    ((is2, ps2), ((ne1', ne2', _))) <- unbind bnd2
                    withIndices (map (\i -> (i, IdxSession)) is2 ++ map (\i -> (i, IdxPId)) ps2) $ do
                            let peq1 = pAnd (pEq (mkSpanned $ AEGet ne1) (mkSpanned $ AEGet ne1'))
                                            (pEq (mkSpanned $ AEGet ne2) (mkSpanned $ AEGet ne2'))
                            let peq2 = pAnd (pEq (mkSpanned $ AEGet ne2) (mkSpanned $ AEGet ne1'))
                                            (pEq (mkSpanned $ AEGet ne1) (mkSpanned $ AEGet ne2'))
                            let pdisj = pNot $ pOr peq1 peq2
                            (_, b) <- SMT.smtTypingQuery "" $ SMT.symAssert pdisj
                            assert ("ODH Disjointness") b

nameExpIsLocal :: NameExp -> Check Bool
nameExpIsLocal ne = 
    case ne^.val of
      NameConst _ (PRes (PDot p s)) [] -> do
          p' <- curModName
          return $ p `aeq` p'
      -- PRFName ne _ -> nameExpIsLocal ne

ensureOnlyLocalNames :: AExpr -> Check ()
ensureOnlyLocalNames ae = withSpan (ae^.spanOf) $ do 
    case ae^.val of
      AEVar _s _ -> return ()
      AEApp _ _ aes -> forM_ aes ensureOnlyLocalNames
      AEHex _ -> return ()
      AEGet n -> do
          b <- nameExpIsLocal n
          assert "Random oracle decl must only involve local names" b
      AEGetEncPK n -> do
          b <- nameExpIsLocal n
          assert "Random oracle decl must only involve local names" b
      AEGetVK n -> do
          b <- nameExpIsLocal n
          assert "Random oracle decl must only involve local names" b
      AEPackIdx _ a -> ensureOnlyLocalNames a
      AELenConst _ -> return ()
      AEInt _ -> return ()

nameTypeUniform :: NameType -> Check ()
nameTypeUniform nt =  
    case nt^.val of
      NT_Nonce -> return ()
      NT_StAEAD _ _ _ -> return ()
      NT_Enc _ -> return ()
      NT_App p ps -> resolveNameTypeApp p ps >>= nameTypeUniform
      NT_MAC _ -> return ()
      NT_KDF _ _ -> return ()
      _ -> typeError $ "Name type must be uniform: " ++ show (owlpretty nt)

-- We then fold the list of decls, checking later ones after processing the
-- earlier ones.
checkDecls :: [Decl] -> Check ()
checkDecls [] = return ()
checkDecls (d:ds) = checkDecl d (checkDecls ds)
--
checkDeclsWithCont :: [Decl] -> Check a -> Check a
checkDeclsWithCont [] k = k
checkDeclsWithCont (d:ds) k = checkDecl d $ checkDeclsWithCont ds k

withTypeErrorHook :: (forall a. String -> Check a) -> Check b -> Check b
withTypeErrorHook f k = do
    local (\e -> e { _typeErrorHook = f }) k 
                                        

checkNoTopLbl :: Label -> Check ()
checkNoTopLbl l = 
    case l^.val of
      LTop -> typeError $ "Top label not allowed here"
      LJoin l1 l2 -> do
          checkNoTopLbl l1
          checkNoTopLbl l2
      LRangeIdx il -> do
          (i, l) <- unbind il
          withIndices [(i, IdxGhost)] $ checkNoTopLbl l
      LGhost -> typeError $ "Ghost label not allowed here"
      _ -> return ()


checkNoTopTy :: Ty -> Check ()
checkNoTopTy t = 
    case t^.val of
      TData l1 l2 _ -> do
          checkNoTopLbl l1
          checkNoTopLbl l2
      TDataWithLength l _ -> checkNoTopLbl l
      TRefined t _ _ -> checkNoTopTy t
      TOption t -> checkNoTopTy t
      TCase _ t1 t2 -> do
          checkNoTopTy t1
          checkNoTopTy t2
      TBool l -> checkNoTopLbl l
      TGhost -> typeError $ "Ghost type not allowed here"
      TUnion t1 t2 -> do
          checkNoTopTy t1
          checkNoTopTy t2
      TAdmit -> typeError $ "Admit type not allowed here"
      TExistsIdx it -> do
          (i, t) <- unbind it
          withIndices [(i, IdxGhost)] $ checkNoTopTy t
      TConst s ps -> do
          td <- getTyDef s
          forM_ ps checkParam
          forM_ ps $ \p -> 
              case p of
                ParamLbl l -> checkNoTopLbl l
                ParamTy t -> checkNoTopTy t
                _ -> return ()
          case td of
            TyAbstract -> return ()
            TyAbbrev t1 -> checkNoTopTy t1
            StructDef ib -> do
                (is, xs) <- unbind ib
                _ <- withIndices (map (\i -> (i, IdxGhost)) is) $ do
                    withDepBind xs $ \args _ -> do 
                        forM_ args $ \(_, _, t) -> checkNoTopTy t
                return ()
            EnumDef b -> do
                ed <- extractEnum ps (show s) b
                forM_ ed $ \(_, ot) -> traverse checkNoTopTy ot
      _ -> return ()      
          



checkNameType :: NameType -> Check ()
checkNameType nt = withSpan (nt^.spanOf) $ 
    case nt^.val of
      NT_DH -> return ()
      NT_Sig t -> do
          checkTy t
          checkNoTopTy t
      NT_Nonce -> return ()
      NT_KDF kdfPos b -> do 
          (((sx, x), (sy, y)), cases) <- unbind b 
          withVars [(x, (ignore sx, Nothing, tGhost)), 
                    (y, (ignore sy, Nothing, tGhost))] $ do
              assert ("KDF cases must be non-empty") $ not $ null cases
              ps <- forM cases $ \bcase -> do
                  (ixs, (p, nts)) <- unbind bcase 
                  withIndices (map (\i -> (i, IdxGhost)) ixs) $ do 
                      checkProp p
                      forM_ nts $ \(str, nt) -> do
                          checkNameType nt
                          nameTypeUniform nt
                      return $ mkExistsIdx ixs p 
              (_, b) <- SMT.smtTypingQuery "disjoint" $ SMT.disjointProps ps
              assert ("KDF disjointness check failed") b
          return ()
      NT_Enc t -> do
        checkTy t
        checkNoTopTy t
        checkTyPubLen t
      NT_App p ps -> do
          resolveNameTypeApp p ps >>= checkNameType
      NT_StAEAD t xaad p -> do
          checkTy t
          checkNoTopTy t
          checkTyPubLen t
          (x, aad) <- unbind xaad
          withVars [(x, (ignore $ show x, Nothing, tGhost))] $ checkProp aad
          checkCounter p
      NT_PKE t -> do
          checkTy t
          checkNoTopTy t
          checkTyPubLen t
      NT_MAC t -> do
          checkTy t
          checkNoTopTy t



checkCounter :: Path -> Check ()
checkCounter p@(PRes (PDot p0 s)) = do
    p' <- curModName
    assert ("Counter must be local: " ++ (show p)) $ p0 `aeq` p'
    md <- openModule p0
    case lookup s (md^.ctrEnv) of
      Just _ -> return ()
      Nothing -> typeError $ "Unknown counter: " ++ show p


checkParam :: FuncParam -> Check ()
checkParam (ParamAExpr a) = do
    _ <- inferAExpr a
    return ()
checkParam (ParamStr s) = return ()
checkParam (ParamLbl l) =  checkLabel l
checkParam (ParamTy t) =  checkTy t
checkParam (ParamIdx i oann) = 
    case oann of
      Nothing -> local (set tcScope $ TcGhost False) $ checkIdx i
      Just IdxSession -> local (set tcScope $ TcGhost False) $ checkIdxSession i
      Just IdxPId -> local (set tcScope $ TcGhost False) $ checkIdxPId i
      Just IdxGhost -> typeError $ "Ghost annotation not supported yet"
checkParam (ParamName ne) = getNameTypeOpt ne >> return ()

checkTy :: Ty -> Check ()
checkTy t = withSpan (t^.spanOf) $ 
    local (set tcScope $ TcGhost False) $
        case t^.val of
          TUnit -> return ()
          TBool l -> checkLabel l
          TGhost -> return ()
          (TData l1 l2 _) -> do
              checkLabel l1
              checkLabel l2
              flowCheck l2 l1
          (TDataWithLength l a) -> do
              checkLabel l
              t <- inferAExpr a
              l' <- coveringLabel t
              flowCheck l' l
          (TRefined t s xp) -> do
              (x, p) <- unbind xp
              checkTy t
              withVars [(x, (ignore s, Nothing, t))] $ checkProp p
          (TOption t) -> do
              checkTy t
          (TConst s ps) -> do
              td <- getTyDef s
              forM_ ps checkParam
              case td of
                TyAbstract -> do
                    assert (show $ owlpretty "Abstract types do not support indices yet") $ length ps == 0
                TyAbbrev t ->
                    assert (show $ owlpretty "Params should be empty for abbrev " <> owlpretty s) $ length ps == 0
                StructDef ib -> do
                    (is, dp) <- unbind ib
                    idxs <- getStructParams ps
                    assert (show $ owlpretty "Wrong index arity for struct " <> owlpretty s) $ length is == length idxs
                EnumDef b -> do
                    _ <- extractEnum ps (show s) b
                    return ()
          (TName n) -> do
              _ <- getNameTypeOpt n
              return ()
          (TExistsIdx it) -> do
              (i, t) <- unbind it
              withIndices [(i, IdxGhost)] $ checkTy t
          (TVK n) -> do
              nt <- getNameType n
              case nt^.val of
                NT_Sig _ -> return ()
                _ -> typeError $ show $ ErrWrongNameType n "sig" nt
          (TDH_PK n) -> do
              nt <- getNameType n
              case nt^.val of
                NT_DH -> return ()
                _ -> typeError $ show $  ErrWrongNameType n "DH" nt
          (TEnc_PK n) -> do
              nt <- getNameType n
              case nt^.val of
                NT_PKE _ -> return ()
                _ -> typeError $ show $ ErrWrongNameType n "PKE" nt
          (TSS n m) -> do
              nt <- getNameType n
              nt' <- getNameType m
              case (nt^.val, nt'^.val) of
                (NT_DH, NT_DH) -> return ()
                (NT_DH, _) -> typeError $ show $ ErrWrongNameType n "DH" nt
                (_, NT_DH) -> typeError $ show $ ErrWrongNameType m "DH" nt
          (TUnion t1 t2) -> do
              checkTy t1
              checkTy t2
          (TCase p t1 t2) -> do
              local (set tcScope $ TcGhost False) $ checkProp p
              checkTy t1
              checkTy t2
          TAdmit -> return ()
          THexConst a -> 
              assert ("HexConst must have even length") $ length a `mod` 2 == 0


tyLenLbl :: Ty -> Check Label
tyLenLbl t =
    case t^.val of
      TName _ -> return zeroLbl
      TVK _ -> return zeroLbl
      TDH_PK _ -> return zeroLbl
      TEnc_PK _ -> return zeroLbl
      TSS _ _ -> return zeroLbl
      TUnit -> return zeroLbl
      TBool _ -> return zeroLbl
      TGhost -> return ghostLbl
      TData _ l _ -> return l
      TDataWithLength _ a -> do
          t <- inferAExpr a
          coveringLabel t
      TRefined t' _ _ -> tyLenLbl t'
      TOption t' -> do
          l' <- tyLenLbl t'
          return $ joinLbl advLbl l'
      TConst s ps -> do
          td <- getTyDef s
          case td of
            TyAbstract -> return advLbl
            TyAbbrev t -> tyLenLbl t
            StructDef b -> do
                (is, xs) <- unbind b
                idxs <- getStructParams ps
                assert ("Wrong index arity for struct " ++ show (owlpretty s)) $ length is == length idxs
                local (set tcScope $ TcGhost False) $ go $ substs (zip is idxs) xs
                    where
                        go (DPDone _) = return zeroLbl
                        go (DPVar t sx xk) = do
                            l1 <- tyLenLbl t
                            (x, k) <- unbind xk
                            l2_ <- withVars [(x, (ignore sx, Nothing, t))] $ go k
                            let l2 = if x `elem` toListOf fv l2_ then (mkSpanned $ LRangeVar $ bind x l2_) else l2_
                            return $ joinLbl l1 l2
            EnumDef b -> do
                bdy <- extractEnum ps (show s) b
                ls <- forM bdy $ \(_, ot) ->
                    case ot of
                      Just t' -> tyLenLbl t'
                      Nothing -> return zeroLbl
                return $ joinLbl advLbl (foldr joinLbl zeroLbl ls)
      (TCase _ t1 t2) -> do
          t' <- normalizeTy t
          case t'^.val of
            TCase p _ _ -> do
                l1 <- tyLenLbl t1
                l2 <- tyLenLbl t2
                return $ joinLbl l1 l2    
            _ -> tyLenLbl t'
      (TUnion t1 t2) -> do
          l1 <- tyLenLbl t1
          l2 <- tyLenLbl t2
          return $ joinLbl l1 l2
      (TExistsIdx it) -> do
          (i, t) <- unbind it
          l <- withIndices [(i, IdxGhost)] $ tyLenLbl t
          return $ mkSpanned $ LRangeIdx $ bind i l
      TAdmit -> return zeroLbl
      THexConst a -> return zeroLbl



checkTyPubLen :: Ty -> Check ()
checkTyPubLen t0 = laxAssertion $ do
    l <- tyLenLbl t0
    flowCheck l advLbl

checkLabel :: Label -> Check ()
checkLabel l =
    local (set tcScope $ TcGhost False) $
        case l^.val of
          (LName n) -> do
              _ <- getNameTypeOpt n
              return ()
          LZero -> return ()
          LAdv -> return ()
          LGhost -> return ()
          LTop -> return ()
          (LJoin l1 l2) -> do
              checkLabel l1
              checkLabel l2
          (LConst (TyLabelVar p))  -> do
              _ <- getTyDef p
              return ()
          (LRangeIdx il) -> do
              (i, l) <- unbind il
              withIndices [(i, IdxGhost)] $ checkLabel l

checkProp :: Prop -> Check ()
checkProp p =
    local (set tcScope $ TcGhost False) $ withSpan  (p^.spanOf) $ 
        case p^.val of
          PTrue -> return ()
          PFalse -> return ()
          (PAnd p1 p2) -> do
              checkProp p1
              checkProp p2
          (POr p1 p2) -> do
              checkProp p1
              checkProp p2
          (PImpl p1 p2) -> do
              checkProp p1
              checkProp p2
          (PNot p) -> checkProp p
          (PFlow l1 l2) -> do
              checkLabel l1
              checkLabel l2
              return ()
          (PQuantIdx _ _ ip) -> do
              (i, p) <- unbind ip
              withIndices [(i, IdxGhost)] $ checkProp p
          (PQuantBV _ _ xp) -> do
              (x, p) <- unbind xp
              withVars [(x, (ignore $ show x, Nothing, tGhost))] $ checkProp p 
          PApp s is xs -> do
              p <- extractPredicate s is xs
              checkProp p
          PAADOf ne x -> do
              _ <- inferAExpr x
              ni <- getNameInfo ne
              case ni of
                Just (nt, _) -> 
                    case nt^.val of
                      NT_StAEAD _ _ _ -> return ()
                      _ -> typeError $ "Wrong name type for " ++ show (owlpretty ne) ++ ": expected StAEAD" 
                Nothing -> typeError $ "Name cannot be abstract here: " ++ show (owlpretty ne)
          PInODH s ikm info -> do
             _ <- inferAExpr s
             _ <- inferAExpr ikm
             _ <- inferAExpr info
             return ()
          (PHappened s (idxs1, idxs2) xs) -> do
              -- TODO: check that method s is in scope?
              _ <- mapM inferAExpr xs
              mapM_ checkIdx idxs1
              mapM_ checkIdx idxs2
              return ()
          PLetIn a xp -> do
              _ <- inferAExpr a 
              (x, p) <- unbind xp
              checkProp $ subst x a p
          (PEq x y) -> do
              _ <- inferAExpr x
              _ <- inferAExpr y
              return ()
          (PValidKDF x y z nks j) -> do
              _ <- mapM inferAExpr [x, y, z]
              assert ("weird case for PValidKDF j") $ j >= 0
              return ()
          (PEqIdx i1 i2) -> do
              checkIdx i1
              checkIdx i2



flowsTo :: Label -> Label -> Check Bool
flowsTo l1' l2' = do
    l1 <- normalizeLabel l1'
    l2 <- normalizeLabel l2'
    tyc <- view tyContext
    (fn, b) <- SMT.checkFlows l1 l2
    case b of
      Just r -> do
        return r
      Nothing -> typeError $ show $ owlpretty "Inconclusive: " <> owlpretty l1 <+> owlpretty "<=" <+> owlpretty l2 
      -- <> line <> owlpretty "Under context: " <> owlprettyTyContext tyc  <> owlpretty fn

tryFlowsTo :: Label -> Label -> Check (Maybe Bool)
tryFlowsTo l1' l2' = do
    l1 <- normalizeLabel l1'
    l2 <- normalizeLabel l2'
    tyc <- view tyContext
    (fn, b) <- SMT.checkFlows l1 l2
    return b

decideProp :: Prop -> Check (Maybe Bool)
decideProp p = do
    tyc <- view tyContext
    (fn, r) <- SMT.symDecideProp p
    return r

flowCheck :: Label -> Label -> Check ()
flowCheck l1 l2 = laxAssertion $ do
    b <- flowsTo l1 l2
    assert (show $ ErrFlowCheck l1 l2) b

-- Ensure l flows to LAdv


stripNameExp :: DataVar -> NameExp -> Check NameExp
stripNameExp x e = 
    case e^.val of
      NameConst _ _ as -> do
          as' <- mapM resolveANF as
          if x `elem` (concat $ map getAExprDataVars as') then
            typeError $ "Cannot remove " ++ show x ++ " from the scope of " ++ show (owlpretty e)
          else
            return e 
      KDFName ann a b c i -> do 
          a' <- resolveANF a
          b' <- resolveANF b
          c' <- resolveANF c
          ann' <- case ann of 
                      KDF_SaltKey ne i -> do
                          ne' <- stripNameExp x ne
                          return $ KDF_SaltKey ne' i
                      KDF_IKMKey ne i -> do
                          ne' <- stripNameExp x ne
                          return $ KDF_IKMKey ne' i
          if x `elem` (getAExprDataVars a' ++ getAExprDataVars b' ++ getAExprDataVars c') then do 
             typeError $ "Cannot remove " ++ show x ++ " from the scope of " ++ show (owlpretty e)
          else return (Spanned (e^.spanOf) $ KDFName ann' a' b' c' i)
      ODHName p ps a c i j -> do 
          a' <- resolveANF a
          c' <- resolveANF c
          if x `elem` (getAExprDataVars a' ++ getAExprDataVars c') then do 
             typeError $ "Cannot remove " ++ show x ++ " from the scope of " ++ show (owlpretty e)
          else return (Spanned (e^.spanOf) $ ODHName p ps a' c' i j)

      
stripLabel :: DataVar -> Label -> Check Label
stripLabel x l = return l

getAExprDataVars :: AExpr -> [DataVar]
getAExprDataVars a = toListOf fv a

getPropDataVars :: Prop -> [DataVar]
getPropDataVars p = toListOf fv p

getLabelDataVars :: Label -> [DataVar]
getLabelDataVars p = toListOf fv p

getTyDataVars :: Ty -> [DataVar]
getTyDataVars p = toListOf fv p

getTyIdxVars :: Ty -> [IdxVar]
getTyIdxVars p = toListOf fv p


-- get strongest type that doesn't mention x
-- t <= stripTy x t
-- p ==> stripProp x p 
-- l <= stripLabel x l

-- Find strongest p' such that p ==> p', and x \notin p'.
-- Always succeeds.
stripProp :: DataVar -> Prop -> Check Prop
stripProp x p =
    case p^.val of
      PTrue -> return p
      PFalse -> return p
      PAnd p1 p2 -> do
          p1' <- stripProp x p1
          p2' <- stripProp x p2
          return $ mkSpanned $ PAnd p1' p2'
      POr p1 p2 -> do
          p1' <- stripProp x p1
          p2' <- stripProp x p2
          return $ mkSpanned $ POr p1' p2'
      PNot p' -> do
          -- If x in p, replace the clause with true
          if x `elem` getPropDataVars p' then return pTrue else return p
      PEq a1 a2 ->
          -- if x in either side, replace clause with true
          if (x `elem` getAExprDataVars a1) || (x `elem` getAExprDataVars a2) then return pTrue else return p
      PEqIdx _ _ -> return p
      PImpl p1 p2 -> do
          if x `elem` getPropDataVars p1 then return pTrue else do
              p2' <- stripProp x p2
              return $ pImpl p1 p2'
      PFlow l1 l2 -> do
          if (x `elem` getLabelDataVars l1) || (x `elem` getLabelDataVars l2) then return pTrue else return p
      PQuantIdx q sx ip -> do
          (i, p') <- unbind ip
          p'' <- stripProp x p'
          return $ mkSpanned $ PQuantIdx q sx (bind i p'')
      PQuantBV q sx xp -> do
          (y, p) <- unbind xp               
          p' <- stripProp x p
          return $ mkSpanned $ PQuantBV q sx (bind y p')
      PHappened s _ xs -> do
          if x `elem` concat (map getAExprDataVars xs) then return pTrue else return p
      PLetIn a yp -> 
          if x `elem` (getAExprDataVars a) then return pTrue else do
            (y, p') <- unbind yp
            p'' <- stripProp x p'
            return $ mkSpanned $ PLetIn a (bind y p'')
      PApp a is xs -> do
          if x `elem` concat (map getAExprDataVars xs) then return pTrue else return p
      PAADOf ne y -> do
          ne' <- stripNameExp x ne
          if x `elem` getAExprDataVars y then return pTrue else return p
      PValidKDF a1 a2 a3 nks j -> do
          if x `elem` (getAExprDataVars a1 ++ getAExprDataVars a2 ++ getAExprDataVars a3) then return pTrue else return p 

stripTy :: DataVar -> Ty -> Check Ty
stripTy x t =
    case t^.val of
      TData l1 l2 s -> do
          l1' <- stripLabel x l1
          l2' <- stripLabel x l2
          return $ Spanned (t^.spanOf) $ TData l1' l2' s
      TDataWithLength l1 ae -> do
          l' <- stripLabel x l1
          if x `elem` getAExprDataVars ae then return $ tData l' l' else return $ tDataWithLength l' ae
      TRefined t1 s yp -> do
          (y, p) <- unbind yp
          t' <- stripTy x t1
          p' <- stripProp x p
          return $ mkSpanned $ TRefined t' s (bind y p')
      TOption t -> do
          t' <- stripTy x t
          return $ mkSpanned $ TOption t'
      TCase p t1 t2 -> do
          withSpan (t^.spanOf) $ 
              assert ("stripTy failed on TCase: free variable " ++ show x ++ " should not appear in proposition of " ++ show (owlpretty t)) $ 
                (not $ x `elem` getPropDataVars p)
          t1' <- stripTy x t1
          t2' <- stripTy x t2
          return $ mkSpanned $ TCase p t1' t2'
      TConst s ps -> do
          forM_ ps $ \p ->
              case p of
                ParamAExpr a ->
                    if x `elem` getAExprDataVars a then typeError "Hard case for TConst" else return ()
                ParamLbl l ->
                    if x `elem` getLabelDataVars l then typeError "Hard case for TConst" else return ()
                ParamTy t ->
                    if x `elem` getTyDataVars t then typeError "Hard case for TConst" else return ()
                _ -> return ()
          return t
      TBool l -> do
          l' <- stripLabel x l
          return $ mkSpanned $ TBool l'
      TGhost -> return t 
      TUnion t1 t2 -> do
          t1' <- stripTy x t1
          t2' <- stripTy x t2
          return $ mkSpanned $ TUnion t1' t2'
      TUnit -> return t
      TName n -> do
          n' <- stripNameExp x n
          return $ mkSpanned $ TName n'
      TVK n -> do
          n' <- stripNameExp x n
          return $ mkSpanned $ TVK n'
      TDH_PK n -> do
          n' <- stripNameExp x n
          return $ mkSpanned $ TDH_PK n'
      TEnc_PK n -> do
          n' <- stripNameExp x n
          return $ mkSpanned $ TEnc_PK n'
      TSS n m -> do
          n' <- stripNameExp x n
          m' <- stripNameExp x m
          return $ mkSpanned $ TSS n' m'
      TAdmit -> return t
      TExistsIdx it -> do
          (i, t) <- unbind it
          t' <- stripTy x t
          return $ mkSpanned $ TExistsIdx $ bind i t
      THexConst a -> return t

stripTys :: [DataVar] -> Ty -> Check Ty
stripTys [] t = return t
stripTys (x:xs) t = do
    t' <- stripTy x t
    stripTys xs t'

checkEndpoint :: Endpoint -> Check ()
checkEndpoint (Endpoint x) = do
    s <- view $ endpointContext
    assert (show $ owlpretty "Unknown endpoint: " <> owlpretty x) $ elem x s
checkEndpoint (EndpointLocality l) = do
    normLocality l
    return ()

getOutTy :: Maybe Ty -> Ty -> Check Ty
getOutTy ot t1 = 
    normalizeTy =<< case ot of 
      Nothing -> return t1
      Just t2 -> do
          assertSubtype t1 t2
          return t2

ensureNonGhost :: Check ()
ensureNonGhost = do
    s <- view tcScope
    assert "Cannot be in ghost here" $ not $ isGhost s 

-- Infer type for expr
checkExpr :: Maybe Ty -> Expr -> Check Ty
checkExpr ot e = withSpan (e^.spanOf) $ pushRoutine ("checkExpr") $ local (set expectedTy ot) $ do 
    case e^.val of
      ECrypt (CLemma lem) aes -> do -- Type check lemma arguments in ghost
          args <- local (set tcScope $ TcGhost False) $ forM aes $ \a -> do
              t <- inferAExpr a
              t' <- normalizeTy t
              return (a, t')
          getOutTy ot =<< checkCryptoOp (CLemma lem) args
      ECrypt cop aes -> do
          args <- forM aes $ \a -> do
              t <- inferAExpr a
              t' <- normalizeTy t
              return (a, t')
          getOutTy ot =<< checkCryptoOp cop args
      (EInput sx xsk) -> do
          ensureNonGhost
          ((x, s), k) <- unbind xsk
          withVars [(x, (ignore $ sx, Nothing, tData advLbl advLbl))] $ local (over (endpointContext) (s :)) $ checkExpr ot k
      (EGetCtr p iargs) -> do 
          checkCounterIsLocal p iargs
          getOutTy ot $ tRefined (tData advLbl advLbl) ".res" $ pEq (aeLength (aeVar ".res")) $ mkSpanned $ AELenConst "counter"
      (EIncCtr p iargs) -> do
          ensureNonGhost
          checkCounterIsLocal p iargs
          getOutTy ot $ tUnit
      (EOutput a ep) -> do
          ensureNonGhost
          case ep of
            Nothing -> return ()
            Just ep -> checkEndpoint ep
          t' <- inferAExpr a
          l_t <- coveringLabel t'
          flowCheck l_t advLbl
          getOutTy ot tUnit
      (EAssert p) -> do
          local (set tcScope $ TcGhost False) $ checkProp p
          (fn, b) <- local (set tcScope $ TcGhost False) $ SMT.smtTypingQuery "assert" $ SMT.symAssert p
          g <- view tyContext
          assert (show $ ErrAssertionFailed fn p) b
          let lineno =  fst $ begin $ unignore $ e^.spanOf
          getOutTy ot $ tRefined tUnit ("assertion_line_" ++ show lineno) p 
      (EAssume p) -> do
          local (set tcScope $ TcGhost False) $ checkProp p
          let lineno =  fst $ begin $ unignore $ e^.spanOf
          getOutTy ot $ tRefined tUnit ("assumption_line_" ++ show lineno) p
      (EAdmit) -> getOutTy ot $ tAdmit
      (EDebug (DebugPrintModules)) -> do
          ms <- view openModules
          getOutTy ot $ tUnit
      (EDebug (DebugResolveANF a)) -> do
          liftIO $ putStrLn $ "esolving ANF on " ++ show (owlpretty a) ++ ":"
          b <- resolveANF a
          liftIO $ putStrLn $ "Got " ++ show (owlpretty b)
          getOutTy ot $ tUnit
      (EDebug (DebugPrint s)) -> do
          liftIO $ putStrLn s
          getOutTy ot $ tUnit
      (EDebug (DebugPrintTyOf s a)) -> do
          t <- local (set tcScope $ TcGhost False) $ inferAExpr a
          a' <- resolveANF a
          t' <- normalizeTy t
          liftIO $ putDoc $ owlpretty "Type for " <> owlpretty s <> owlpretty ": " <> owlpretty t' <> line
          getOutTy ot $ tUnit
      (EDebug (DebugHasType s a t)) -> do
          checkTy t
          ta <- local (set tcScope $ TcGhost False) $ inferAExpr a
          b <- isSubtype ta t
          liftIO $ putDoc $ owlpretty s <+> owlpretty "has type" <+> owlpretty t <> owlpretty ":" <+> owlpretty b <> line
          getOutTy ot $ tUnit
      (EDebug (DebugPrintTy t)) -> do
          t' <- normalizeTy t
          liftIO $ putStrLn $ show $ owlpretty t <+> owlpretty "normalizes to: " <> owlpretty t'
          getOutTy ot $ tUnit
      (EDebug (DebugPrintProp p)) -> do
          liftIO $ putDoc $ owlpretty p
          getOutTy ot $ tUnit
      (EDebug (DebugPrintTyContext anf)) -> do
          tC <- view tyContext
          let tC' = if anf then removeAnfVars tC else tC
          liftIO $ putDoc $ owlprettyTyContext tC'
          getOutTy ot $ tUnit
      (EDebug (DebugPrintExpr e)) -> do
          liftIO $ putStrLn $ show $ owlpretty e
          getOutTy ot $ tUnit
      (EDebug (DebugPrintLabel l)) -> do
          liftIO $ putStrLn $ show $ owlpretty l
          getOutTy ot $ tUnit
      (EUnionCase a s xe) -> do
          t <- inferAExpr a
          (x, e) <- unbind xe
          case (stripRefinements t)^.val of
            TUnion t1 t2 -> do
                logTypecheck $ owlpretty $ "First case for EUnionCase: " ++ s
                pushLogTypecheckScope
                t1' <- withVars [(x, (ignore s, Nothing, tRefined t1 ".res" (pEq (aeVar ".res") a)))] $ checkExpr ot e
                popLogTypecheckScope
                logTypecheck $ owlpretty $ "Second case for EUnionCase: " ++ s
                pushLogTypecheckScope
                t2' <- withVars [(x, (ignore s, Nothing, tRefined t2 ".res" (pEq (aeVar ".res") a)))] $ checkExpr ot e
                popLogTypecheckScope
                assertSubtype t1' t2'
                getOutTy ot =<< stripTy x t2'
            _ -> do  -- Just continue
                t <- withVars [(x, (ignore s, Nothing, t))] $ checkExpr ot e
                getOutTy ot =<< stripTy x t
      (EBlock k p) -> do
          tc <- view tcScope
          let tc' = case (tc, p) of
                      (TcDef _, True) -> TcGhost True
                      (TcGhost True, True) -> TcGhost True
                      _ -> tc
          local (set tcScope tc') $ checkExpr ot k
      (ELet e tyAnn anf sx xe') -> do
          let letTriv = xe' `aeq` (bind (s2n ".res") $ mkSpanned $ ERet (aeVar ".res"))
          tyAnn' <- case tyAnn of
            Just t -> do
                checkTy t
                return $ Just t
            Nothing -> do
                return $ if letTriv then ot else Nothing
          t1 <- checkExpr tyAnn' e 
          tc <- view tcScope
          (x, e') <- unbind xe'
          t2 <- withVars [(x, (ignore sx, anf, t1))] (checkExpr ot e')
          stripTy x t2
      ELetGhost a sx xk -> do
          t <- local (set tcScope $ TcGhost False) $ inferAExpr a
          t' <- normalizeTy t
          t'' <- ghostifyTy a t'
          (x, k) <- unbind xk
          t2 <- withVars [(x, (ignore sx, Nothing, t''))] (checkExpr ot k)
          stripTy x t2
      (EChooseIdx ip ik) -> do
          (ix, p) <- unbind ip
          withIndices [(ix, IdxGhost)] $ do
              checkProp p
          (_, b) <- SMT.symDecideProp $ mkSpanned $ PQuantIdx Exists (ignore $ show ix) ip
          (i, k) <- unbind ik
          getOutTy ot =<< case b of
            Just True -> do
                x <- freshVar
                let tx = tLemma (subst ix (mkIVar i) p) 
                to <- withIndices [(i, IdxGhost)] $ do
                    withVars [(s2n x, (ignore x, Nothing, tx))] $ checkExpr ot k
                if i `elem` getTyIdxVars to then
                    return (tExistsIdx (bind i to))
                else return to
            _ -> do
                t' <- withIndices [(i, IdxGhost)] $ checkExpr ot k
                if i `elem` getTyIdxVars t' then
                    return (tExistsIdx (bind i t'))
                else return t'
      (EUnpack a (si, sx) ixk) -> do
          t <- inferAExpr a
          ((i, x), e_) <- unbind ixk
          let e = subst i (mkIVar (s2n si)) e_ 
          getOutTy ot =<< case (stripRefinements t)^.val of
            TExistsIdx jt' -> do
                (j, t') <- unbind jt'
                let tx = tRefined (subst j (mkIVar $ s2n si) t') ".res" (pEq (aeVar ".res") a) 
                to <- withIndices [(s2n si, IdxGhost)] $ do 
                    withVars [(x, (ignore $ sx, Nothing, tx))] $ checkExpr ot e
                to' <- stripTy x to
                if (s2n si) `elem` getTyIdxVars to' then
                    return (tExistsIdx (bind i to'))
                else return to'
            _ -> do
                t' <- withIndices [(s2n si, IdxGhost)] $ withVars [(x, (ignore sx, Nothing, t))] $ checkExpr ot e
                to' <- stripTy x t'
                if (s2n si) `elem` getTyIdxVars to' then
                    return (tExistsIdx (bind i to'))
                else return to'
      (ETLookup pth@(PRes (PDot p n)) a) -> do
          md <- openModule p
          case lookup n (md^.tableEnv) of 
            Nothing -> typeError $ show $  owlpretty "Unknown table: " <> owlpretty n
            Just (t, loc) -> do
                tc <- view tcScope
                ta <- inferAExpr a
                assertSubtype ta (tData advLbl advLbl)
                case tc of
                  TcDef curr_loc -> do
                      curr_loc' <- normLocality curr_loc
                      loc' <- normLocality loc
                      assert (show $ owlpretty "Wrong locality for table: got" <> owlpretty curr_loc <+> owlpretty "but expected" <+> owlpretty loc) $ curr_loc' `aeq` loc'
                      getOutTy ot $ mkSpanned $ TOption t
                  _ -> typeError $ "Weird case: should be in a def"
      (ETWrite pth@(PRes (PDot p n)) a1 a2) -> do
          ensureNonGhost
          md <- openModule p
          case lookup n (md^.tableEnv) of 
            Nothing -> typeError $ show $ owlpretty "Unknown table: " <> owlpretty n
            Just (t, loc) -> do
                tc <- view tcScope
                case tc of
                  TcDef curr_loc -> do
                      curr_loc' <- normLocality curr_loc
                      loc' <- normLocality loc
                      assert (show $ owlpretty "Wrong locality for table: got" <> owlpretty curr_loc <+> owlpretty "but expected" <+> owlpretty loc) $ curr_loc' `aeq` loc'
                      ta <- inferAExpr a1
                      assertSubtype ta (tData advLbl advLbl)
                      ta2 <- inferAExpr a2
                      assertSubtype ta2 t
                      getOutTy ot $ tUnit

      (ECall f (is1, is2) args) -> do
          ensureNonGhost -- TODO: fix for ghost methods
          bfdef <- getDefSpec f
          ts <- view tcScope
          ((bi1, bi2), dspec) <- unbind bfdef
          assert (show $ owlpretty "Wrong index arity for " <> owlpretty f) $ length is1 == length bi1
          assert (show $ owlpretty "Wrong index arity for " <> owlpretty f) $ length is2 == length bi2
          forM_ is1 checkIdxSession
          forM_ is2 checkIdxPId
          let (DefSpec _ fl o) = substs (zip bi1 is1) $ substs (zip bi2 is2) dspec
          case ts of
            TcDef curr_locality -> do
                fl' <- normLocality fl
                curr_locality' <- normLocality curr_locality
                assert (show $ owlpretty "Wrong locality for function call") $ fl' `aeq` curr_locality'
                let go (db :: DepBind (Prop, Ty, Maybe Expr)) args = 
                        case (db, args) of 
                          (DPDone v, []) -> return v
                          (DPDone _, _) -> typeError $ "Too many arguments for " ++ show (owlpretty f)
                          (DPVar _ _ _, []) -> typeError $ "Too few arguments for " ++ show (owlpretty f)
                          (DPVar t _ xd, a:as) -> do 
                             t' <- inferAExpr a
                             assertSubtype t' t
                             (x, d) <- unbind xd
                             go (subst x a d) as
                (prereq, retTy, _) <- go o args
                (fn, b) <- SMT.smtTypingQuery "precond" $ SMT.symAssert prereq
                assert ("Precondition failed: " ++ show (owlpretty prereq) ++ show (owlpretty fn)) b
                let happenedProp = pHappened f (is1, is2) args
                getOutTy ot $ (tRefined retTy ".res" happenedProp)
            _ -> typeError $ "Unreachable"
      (EIf a e1 e2) -> do
          t <- inferAExpr a
          lt <- coveringLabel t
          flowCheck lt advLbl
          -- Carry forward refinements from t into the path condition
          t' <- normalizeTy t
          pathRefinement <- case t' ^. val of
            TRefined _ _ xp -> do
                (x, p) <- unbind xp
                return $ subst x a p 
            _ -> return pTrue
          x <- freshVar
          t1 <- withVars [(s2n x, (ignore x, Nothing, tRefined tUnit ".pCond" (pAnd (pEq a aeTrue) pathRefinement)))] $ checkExpr ot e1
          t2 <- withVars [(s2n x, (ignore x, Nothing, tRefined tUnit ".pCond" (pAnd (pNot $ pEq a aeTrue) pathRefinement)))] $ checkExpr ot e2
          case ot of 
            Just t3 -> return t3
            Nothing -> do
                t1' <- stripTy (s2n x) t1
                assertSubtype t2 t1'
                return t1'
      EGuard a k -> do
          ensureNonGhost
          t <- inferAExpr a
          b <- tyFlowsTo t advLbl
          withSpan (a^.spanOf) $ assert ("Guard must be public") b   
          t' <- normalizeTy t
          pathRefinement <- case t'^.val of
                              TRefined _ _ xp -> do
                                  (x, p) <- unbind xp
                                  return $ subst x a p
                              _ -> return pTrue
          x <- freshVar
          t1 <- withVars [(s2n x, (ignore x, Nothing, tRefined tUnit ".pCond" (pAnd (pEq a aeTrue) pathRefinement)))] $ checkExpr ot k
          case t1^.val of
            TOption _ -> stripTy (s2n x) t1 
            _ -> typeError $ "Guard body must return an option: " ++ show (owlpretty t1)
      (ERet a) -> do
          t <- inferAExpr a
          getOutTy ot $ tRefined t ".res" (pEq (aeVar ".res") a)
      EFalseElim e op -> do
          doFalseElim <- case op of
                           Nothing -> return True
                           Just pcond -> do
                             _ <- local (set tcScope $ TcGhost False) $ checkProp pcond
                             (_, b) <- SMT.smtTypingQuery "false_elim condition" $ SMT.symAssert pcond
                             return b 
          case doFalseElim of
            True -> do
               (_, b) <- SMT.smtTypingQuery "false_elim" $ SMT.symAssert $ mkSpanned PFalse
               if b then getOutTy ot tAdmit else checkExpr ot e
            False -> checkExpr ot e
      (ESetOption s1 s2 k) -> do
        local (over z3Options $ M.insert s1 s2) $ checkExpr ot k
      (EForallBV s xk) -> do
          (x, k) <- unbind xk
          t <- local (set tcScope $ TcGhost False) $ withVars [(x, (ignore s, Nothing, tGhost))] $ do
              checkExpr Nothing k
          t' <- normalizeTy t
          case t'^.val of
            TRefined (Spanned _ TUnit) _ yp -> do
                (y, p') <- unbind yp
                getOutTy ot $ tLemma $ mkSpanned $ PQuantBV Forall (ignore s) $ bind x $ subst y (aeApp (topLevelPath "unit") [] []) p'
            _ -> typeError $ "Unexpected return type of forall body: " ++ show (owlpretty t')
      (EForallIdx s ik) -> do
          (i, k) <- unbind ik
          tc <- view tcScope
          -- We allow crypto lemmas underneath forall_idx, because there are
          -- only polynomially many indices.
          -- If we already disallow crypto lemmas, though, continue to forbid
          -- them
          let tc' = case tc of
                      TcGhost False -> TcGhost False
                      _ -> TcGhost True
          t <- local (set tcScope $ tc') $ withIndices [(i, IdxGhost)] $ do
              checkExpr Nothing k
          t' <- normalizeTy t
          case t'^.val of
            TRefined (Spanned _ TUnit) _ yp -> do
                (y, p') <- unbind yp
                getOutTy ot $ tLemma $ mkSpanned $ PQuantIdx Forall (ignore s) $ bind i $ subst y (aeApp (topLevelPath "unit") [] []) p'
            _ -> typeError $ "Unexpected return type of forall body: " ++ show (owlpretty t')
      (ECorrCaseNameOf a op k) -> do
          t <- inferAExpr a
          t' <- normalizeTy t
          case extractNameFromType t' of
            Just n ->  checkExpr ot $ Spanned (e^.spanOf) $ EPCase (pFlow (nameLbl n) advLbl) op k
            Nothing -> checkExpr ot k
      (EPCase p op k) -> do
          _ <- local (set tcScope $ TcGhost False) $ checkProp p
          doCaseSplit <- case op of
                           Nothing -> return True
                           Just pcond -> do 
                               _ <- local (set tcScope $ TcGhost False) $ checkProp pcond
                               (_, b) <- SMT.smtTypingQuery "case split condition" $ SMT.symAssert pcond
                               return b 
          retT <- case ot of
                    Just t -> return t
                    Nothing -> typeError $ "pcase must have expected return type"
          case doCaseSplit of 
            False -> checkExpr ot k
            True -> do 
              let pcase_line = fst $ begin $ unignore $ e^.spanOf
              x <- freshVar
              _ <- withVars [(s2n x, (ignore $ "pcase_true (line " ++ show pcase_line ++ ")", Nothing, tLemma p))] $ do
                  logTypecheck $ owlpretty "Case split: " <> owlpretty p
                  pushLogTypecheckScope
                  (_, b) <- SMT.smtTypingQuery "case split prune" $ SMT.symAssert $ mkSpanned PFalse
                  r <- if b then getOutTy ot tAdmit else checkExpr (Just retT) k
                  popLogTypecheckScope
              _ <- withVars [(s2n x, (ignore $ "pcase_false (line " ++ show pcase_line ++ ")", Nothing, tLemma (pNot p)))] $ do
                  logTypecheck $ owlpretty "Case split: " <> owlpretty (pNot p)
                  pushLogTypecheckScope
                  (_, b) <- SMT.smtTypingQuery "case split prune" $ SMT.symAssert $ mkSpanned PFalse
                  r <- if b then getOutTy ot tAdmit else checkExpr (Just retT) k
                  popLogTypecheckScope
              normalizeTy retT
      EParse a t ok bk -> do
          t1 <- inferAExpr a
          checkTy t
          sinfo <- obtainStructInfoTopDown a t
          b <- isSubtype t1 t
          otherwiseCase <- case ok of
                             Nothing -> return Nothing
                             Just k' -> Just <$> checkExpr ot k'
          case b of
            True -> do -- Well-typed case
                (b, k) <- unbind bk
                assert ("Wrong number of variables on struct " ++ show (owlpretty t)) $ length b == length sinfo
                bindings <- forM (zip b sinfo) $ \((x, s), (_, t)) -> do 
                    return (x, (s, Nothing, t))
                tk <- withVars bindings $ do
                    tC <- view tyContext
                    checkExpr ot k   
                stripTys (map fst b) tk
            False -> do -- Ill-typed case
                (b, k) <- unbind bk
                assert ("Wrong number of variables on struct " ++ show (owlpretty t)) $ length b == length sinfo
                l <- coveringLabel t1
                validatedTys <- getValidatedStructTys (show $ owlpretty t) l sinfo
                -- let lt = tData l l 
                -- tk <- withVars (map (\(x, s) -> (x, (s, Nothing, lt))) b) $ checkExpr ot k   
                let tc2 = map (\((x, s), (_, t)) -> (x, (s, Nothing, t))) (zip b validatedTys)
                tk_otherwise <- case otherwiseCase of
                         Nothing -> typeError "Parse statement needs an otherwise case here"
                         Just t' -> return t'
                tk <- (withVars tc2 $ checkExpr ot k) >>= stripTys (map fst b) 
                assertSubtype tk_otherwise tk
                return tk
      (ECase e1 otk cases) -> do
          t <- checkExpr Nothing e1
          t <- stripRefinements <$> normalizeTy t
          (wfCase, tcases, ok) <- case otk of
            Just (tAnn, k) -> do
                checkTy tAnn
                tAnn' <- normalizeTy tAnn
                tc <- withSpan (e1^.spanOf) $ obtainTyCases tAnn' ""
                b <- isSubtype t tAnn'
                return (b, tc, Just k)
            Nothing -> do
                tc <- withSpan (e1^.spanOf) $ obtainTyCases t ". Try adding an annotation to the case statement."
                return (True, tc, Nothing)
          lt <- coveringLabel t
          when (not wfCase) $ do
              flowCheck lt advLbl
          assert ("Duplicate case") $ uniq (map fst cases)
          assert ("Cases must not be nonempty") $ length cases > 0
          assert ("Cases are not exhaustive") $ (S.fromList (map fst cases)) == (S.fromList (map fst tcases))
          branch_ts <- forM cases $ \(c, ocase) -> do
              let (Just otcase) = lookup c tcases
              case (otcase, ocase) of
                (Nothing, Left ek) -> checkExpr ot ek
                (Just t1, Right (s, xk)) -> do
                    (x, k) <- unbind xk
                    -- Generate type of bound case variable. Note that if this is a parsing `case` statement,
                    -- we need to generate a type that incorporates the length information obtained from parsing.
                    -- For enums, the payload is allowed to have an unknown length, since it can be parsed with a
                    -- `tail` combinator.
                    xt <- if wfCase then return t1 else do
                        t' <- getValidatedTy lt t1
                        return $ case t' of
                            Nothing -> tData lt lt
                            Just t' -> t'
                    tout <- withVars [(x, (s, Nothing, xt))] $ checkExpr ot k
                    case ot of
                      Just _ -> return tout
                      Nothing -> stripTy x tout
                _ -> do
                    let ar1 = case otcase of
                                  Nothing -> 0
                                  Just _ -> 1
                    let ar2 = case ocase of
                                  Left _ -> 0
                                  Right _ -> 1
                    typeError $ "Mismatch on branch case" ++ c ++ ": expected arity " ++ show ar1 ++ ", got " ++ show ar2
          branch_ts' <- case ok of
                          Nothing -> return branch_ts
                          Just k -> do 
                              t <- checkExpr ot k
                              return (t : branch_ts)
          case ot of
            Just tout -> return tout
            Nothing -> do -- Need to synthesize type here. Take the first one
                let t = head branch_ts'
                forM_ (tail branch_ts) $ \t' -> assertSubtype t' t
                return t

ghostifyTy :: AExpr -> Ty -> Check Ty
ghostifyTy a t = do
    let tghost = case t^.val of 
                  TRefined _ s xk -> Spanned (t^.spanOf) $ TRefined tGhost s xk
                  _ -> tGhost
    return $ tRefined tghost ".res" (pEq a (aeVar ".res"))

-- Generate types for the parsed struct fields that incorporate the length information generated from parsing.
-- Note: we allow the last field in the struct to have a statically unknowable length, since it can be parsed with 
-- a `tail` combinator.
getValidatedStructTys :: String -> Label -> [(String, Ty)] -> Check [(String, Ty)]
getValidatedStructTys structTy albl sinfo = do
    maybeTys <- mapM (\(n,t) -> getValidatedTy albl t) sinfo
    case allowLastUnknownLen (tData albl albl) maybeTys of
        Nothing -> do
            warn $ "Unparsable struct type: " ++ structTy ++ ", no length info generated from parsing"
            return $ zip (map fst sinfo) (repeat $ tData albl albl)
        Just tys -> return $ zip (map fst sinfo) tys
    where
    -- Like `Data.Traversable.sequence`, but uses the default value for the last element if it is `Nothing`.
    allowLastUnknownLen :: a -> [Maybe a] -> Maybe [a]
    allowLastUnknownLen _ [] = Just []
    allowLastUnknownLen def [Nothing] = Just [def]
    allowLastUnknownLen def (h:t) = (:) <$> h <*> allowLastUnknownLen def t

getValidatedTy :: Label -> Ty -> Check (Maybe Ty)
getValidatedTy albl t = local (set tcScope $ TcGhost False) $ do
    case t ^. val of
        TData _ _ _ -> do
            return Nothing
        TDataWithLength _ ae -> do
            t <- inferAExpr ae
            l <- tyLenLbl t
            b <- flowsTo l zeroLbl
            return $ if b then Just $ tDataWithLength albl ae else Nothing
        TRefined t' _ _ -> getValidatedTy albl t' -- Refinement not guaranteed to hold by parsing
        TOption t' -> do 
            t'' <- getValidatedTy albl t'
            case t'' of
              Nothing -> return Nothing
              Just t'' -> return $ Just $ mkSpanned $ TOption t''
        TCase _ _ _ -> return Nothing
        TConst s ps -> do
            td <- getTyDef s
            case td of
              EnumDef b -> do
                -- Check that all cases are validatable:
                caseTys <- mapMaybe snd <$> extractEnum ps (show s) b
                validatedTys <- mapM (getValidatedTy albl) caseTys
                case sequence validatedTys of
                    Nothing -> do
                        warn $ "Unparsable enum type: " ++ show (owlpretty s) ++ ", no length info generated from parsing"
                        return Nothing -- Unparsable nested enum type
                    Just _ -> 
                        -- All cases are parsable, but since we don't have a structural representation of the validated
                        -- enum, we just return Data<albl> and require a second `case` statement to parse it.
                        return $ Just $ tData albl albl 
              StructDef b -> do
                (is, dp) <- unbind b
                idxs <- getStructParams ps
                assert ("Wrong index arity for struct") $ length idxs == length is
                withIndices (map (\i -> (i, IdxGhost)) is) $ do
                    res <- withDepBind dp $ \args _ -> do
                        validatedTys <- mapM (getValidatedTy albl) (map (\(_, _, t) -> t) args)
                        case sequence validatedTys of
                            Nothing -> do
                                warn $ "Unparsable struct type: " ++ show (owlpretty s) ++ ", no length info generated from parsing"
                                return Nothing -- Unparsable nested struct type
                            Just _ -> do
                                -- All cases are parsable, but since we don't have a structural representation of the validated
                                -- struct, we just return Data<albl> and require a second `parse` statement to parse it.
                                return $ Just $ tData albl albl
                    return $ unsafeMapDepBind res id
              TyAbbrev t' -> getValidatedTy albl t'
              TyAbstract -> typeError $ "Abstract type " ++ show (owlpretty t) ++ " is unparsable"
        TBool _ -> return $ Just $ mkSpanned $ TBool albl
        TGhost -> return $ Just t
        TUnion _ _ -> return Nothing
        TUnit -> return $ Just tUnit
        TName ne -> do
            nameLen <- getLenConst ne
            return $ Just $ tDataWithLength albl nameLen
        TVK _ -> return $ Just $ tDataWithLength albl (aeLenConst "vk")
        TDH_PK _ -> return $ Just $ tDataWithLength albl (aeLenConst "group")
        TEnc_PK _ -> return $ Just $ tDataWithLength albl (aeLenConst "pke_pk")
        TSS _ _ -> return $ Just $ tDataWithLength albl (aeLenConst "group")
        TAdmit -> typeError $ "Unparsable type: " ++ show (owlpretty t)
        TExistsIdx ity -> do
            (i, ty) <- unbind ity
            withIndices [(i, IdxGhost)] $ getValidatedTy albl ty
        THexConst a -> return $ Just t 
    where     
    getLenConst :: NameExp -> Check AExpr
    getLenConst ne = do
        ntLclsOpt <- getNameInfo ne
        case ntLclsOpt of
            Nothing -> typeError $ "Name shouldn't be abstract: " ++ show (owlpretty ne)
            Just (nt, _) ->  go nt
                where
                    go nt = 
                        case nt^.val of
                            NT_Nonce -> return $ mkSpanned $ AELenConst "nonce"
                            NT_Enc _ -> return $ mkSpanned $ AELenConst "enckey"
                            NT_App p ps -> resolveNameTypeApp p ps >>= go
                            NT_StAEAD _ _ _ -> return $ mkSpanned $ AELenConst "enckey"
                            NT_MAC _ -> return $ mkSpanned $ AELenConst "mackey"
                            NT_DH -> return $ mkSpanned $ AELenConst "group"
                            NT_Sig _ -> return $ mkSpanned $ AELenConst "signature"
                            NT_PKE _ -> return $ mkSpanned $ AELenConst "pke_sk"
                            NT_KDF _ _ -> return $ mkSpanned $ AELenConst "kdfkey"
                    -- NT_PRF _ -> typeError $ "Unparsable name type: " ++ show (owlpretty nt)

doAEnc t1 x t args =
  case extractNameFromType t1 of
    Just k -> do
        nt <- local (set tcScope $ TcGhost False) $  getNameType k
        case nt^.val of
          NT_Enc t' -> do
              b1 <- isSubtype t t'
              if b1 then
                  return $ mkSpanned $ TRefined (tData advLbl advLbl) ".res" $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (aeApp (topLevelPath $ "cipherlen") [] [aeLength x])
              else
                  mkSpanned <$> trivialTypeOf [t1, t]
          _ -> typeError $ show $ ErrWrongNameType k "encryption key" nt
    _ -> do
        mkSpanned <$> trivialTypeOf [t1, t]

doADec t1 t args = do
    case extractNameFromType t1 of
      Just k -> do
          nt <-  local (set tcScope $ TcGhost False) $ getNameType k
          case nt^.val of
            NT_Enc t' -> do
                b2 <- flowsTo (nameLbl k) advLbl
                b <- tyFlowsTo t advLbl -- Public ciphertext
                if ((not b2) && b) then do
                    -- Honest
                    return $ mkSpanned $ TOption t'
                else if (b && b2) then do
                    return $ mkSpanned $ TOption $ tDataAnn advLbl advLbl "Corrupt adec"
                else do
                    l_corr <- coveringLabelOf [t1, t]
                    -- Corrupt
                    return $ tDataAnn l_corr l_corr "Corrupt adec"
            _ -> typeError $ show $  ErrWrongNameType k "encryption key" nt
      _ -> do
          b1 <- tyFlowsTo t1 advLbl
          b2 <- tyFlowsTo t advLbl
          if b1 && b2 then return (mkSpanned $ TOption $ tDataAnn advLbl advLbl "Corrupt adec")
          else do 
              l <- coveringLabelOf [t1, t]
              return $ tData l l 

owlprettyMaybe :: OwlPretty a => Maybe a -> OwlDoc
owlprettyMaybe x = 
    case x of
      Nothing -> owlpretty "Nothing"
      Just x -> owlpretty "Just" <+> owlpretty x

pNameExpEq :: NameExp -> NameExp -> Check Prop
pNameExpEq ne1 ne2 = do
    ni1 <- getNameInfo ne1
    ni2 <- getNameInfo ne2
    case (ni1, ni2) of
      (Just (_, Just (pth1, _)), Just (_, Just (pth2, _))) | (not $ aeq pth1 pth2) -> return pFalse
      _ -> return $ pEq (mkSpanned $ AEGet ne1) (mkSpanned $ AEGet ne2)

nameExpNotIn :: NameExp -> [NameExp] -> Check Prop
nameExpNotIn ne nes = do
    ps <- mapM (\ne' -> pNot <$> pNameExpEq ne ne') nes
    return $ foldr pAnd pTrue ps

proveDisjointContents :: AExpr -> AExpr -> Check ()
proveDisjointContents x y = do
    ns1 <- getNameContents x
    ns2 <- getNameContents y
    ns1' <- mapM normalizeNameExp ns1
    ns2' <- mapM normalizeNameExp ns2
    p1 <- foldr pAnd pTrue <$> mapM (\ne -> nameExpNotIn ne ns2') ns1' 
    p2 <- foldr pAnd pTrue <$> mapM (\ne -> nameExpNotIn ne ns1') ns2' 
    local (set tcScope $ TcGhost False) $ do
        (_, b) <- SMT.smtTypingQuery "proveDisjoint" $ SMT.symAssert $ pOr p1 p2
        assert ("Cannot prove disjointness of " ++ show (owlpretty x) ++ " and " ++ show (owlpretty y) ++ ": got " ++ show (owlpretty ns1') ++ " and " ++ show (owlpretty ns2')) $ b
        where
            -- Computes the set of names that are contained verbatim in the
            -- expression
            getNameContents :: AExpr -> Check [NameExp]
            getNameContents a = withSpan (a^.spanOf) $
                case a^.val of
                  _ | isConstant a -> return []
                  AEGet ne -> return [ne]
                  AEApp f _ xs -> do
                      case f of
                        _ | f `aeq` topLevelPath "concat" -> do
                            ns <- mapM getNameContents xs
                            return $ concat ns
                        _ | f `aeq` topLevelPath "dhpk" -> return []
                        _ -> typeError $ "Unsupported function in disjoint_not_eq_lemma: " ++ show (owlpretty f)
                  _ -> typeError $ "Unsupported expression in disjoint_not_eq_lemma: " ++ show (owlpretty a)


data KDFInferResult = KDFAdv | KDFGood KDFStrictness NameExp | KDFCorrupt Label [(KDFStrictness, NameType)]
    deriving (Show, Generic, Typeable)

instance OwlPretty KDFInferResult where
    owlpretty KDFAdv = owlpretty "KDFAdv"
    owlpretty (KDFGood str ne) = owlpretty "KDFGood(" <> owlpretty ne <> owlpretty ")"
    owlpretty (KDFCorrupt l nts) = owlpretty "KDFCorrupt(" <> owlpretty l <> owlpretty ")"

instance Alpha KDFInferResult

unifyKDFInferResult :: 
    KDFSelector ->
    Either KDFSelector (String, ([Idx], [Idx]), KDFSelector)
    ->
    KDFInferResult -> KDFInferResult -> Check KDFInferResult
unifyKDFInferResult _ _ (KDFCorrupt _ _) v = return v
unifyKDFInferResult _ _ v (KDFCorrupt _ _) = return v
unifyKDFInferResult _ _ (KDFAdv) v = return v
unifyKDFInferResult _ _ v KDFAdv = return v
unifyKDFInferResult i e v1@(KDFGood str ne_) (KDFGood str' ne_') = do
    ne <- normalizeNameExp ne_
    ne' <- normalizeNameExp ne_'
    b <- SMT.symEqNameExp ne ne'
    ni1 <- getNameInfo ne
    ni2 <- getNameInfo ne'
    let b2 = (str == str')
    b3 <- case (ni1, ni2) of
               (Nothing, Nothing) -> return True
               (Just (nt1, _), Just (nt2, _)) -> return $ nt1 `aeq` nt2
               (_, _) -> return False
    let pe = case e of
                Left i -> owlpretty i
                Right (s, ips, i) -> list [owlpretty s, owlpretty ips, owlpretty i]
    case (b && b2 && b3) of
      True -> return v1
      _ | not b3 -> do
          typeError $ "KDF results inconsistent: mismatch on name types for selectors "  ++ show (owlprettyKDFSelector i) ++ ", " ++ show pe
      _ | not b2 -> typeError $ "KDF results inconsistent: mismatch on strictness for selectors " ++ show (owlprettyKDFSelector i) ++ ", " ++ show pe
      _ | not b -> typeError $ "KDF results inconsistent: result name types not equal for selectors " ++ show (owlprettyKDFSelector i) ++ ", " ++ show pe

inferKDF :: KDFPos -> (AExpr, Ty) -> (AExpr, Ty) -> (AExpr, Ty) -> 
            KDFSelector -> Int -> [NameKind] -> Check (Maybe KDFInferResult)
inferKDF kpos a b c (i, is_case) j nks = do
    mapM_ inferIdx is_case
    let (principal, other) = case kpos of
                              KDF_SaltPos -> (a, b)
                              KDF_IKMPos -> (b, a)
    case extractNameFromType (snd principal) of 
      Nothing -> return Nothing
      Just ne -> do
        wf <- isSubtype (snd principal) (tName ne)
        case wf of
          False -> return Nothing
          True -> do 
              nt <- getNameType ne
              case nt^.val of
                NT_KDF kpos' bcases | kpos `aeq` kpos' -> do
                    (((sx, x), (sy, y)), cases_) <- unbind bcases
                    let cases = subst x (fst other) $ subst y (fst c) $ cases_
                    assert "KDF case out of bounds" $ i < length cases                    
                    (ixs, pnts) <- unbind $ cases !! i
                    assert ("KDF case index arity mismatch") $ length ixs == length is_case
                    let (p, nts) = substs (zip ixs is_case) $ pnts
                    nks2 <- forM nts $ \(_, nt) -> getNameKind nt
                    assert ("Mismatch on name kinds for kdf: annotation says " ++ show (owlpretty $ NameKindRow nks) ++ " but key says " ++ show (owlpretty $ NameKindRow nks2)) $ nks == nks2
                    assert "KDF row index out of bounds" $ j < length nts                    
                    let (str, _) = nts !! j
                    bp <- decideProp p
                    b2 <- not <$> flowsTo (nameLbl ne) advLbl
                    let ann = case kpos of
                                KDF_SaltPos -> KDF_SaltKey ne (i, is_case)
                                KDF_IKMPos -> KDF_IKMKey ne (i, is_case)
                    if (bp == Just True) then
                          if b2 then 
                                return $ Just $ KDFGood str $ 
                                    mkSpanned $ KDFName ann (fst a) (fst b) (fst c) j   
                          else do
                              l_corr <- coveringLabelOf [snd a, snd b, snd c]
                              return $ Just $ KDFCorrupt l_corr nts 
                    else return Nothing
                NT_KDF kpos' _ -> typeError $ "Unexpected key position: expected " ++ show (kpos') ++ " but got " ++ show kpos

-- Try to infer a valid local DH computation (pk, sk) from input
-- (local = sk name is local to the module)
getLocalDHComputation :: AExpr -> Check (Maybe (AExpr, NameExp))
getLocalDHComputation a = do
    let dhpk x = mkSpanned $ AEApp (topLevelPath "dhpk") [] [x]
    let go_from_ty = do
            t <- inferAExpr a
            case (stripRefinements t)^.val of
              TSS n m -> do
                  m_local <- nameExpIsLocal m
                  n_local <- nameExpIsLocal n
                  if m_local then return (Just (dhpk (aeGet n), m)) else 
                     if n_local then return (Just (dhpk (aeGet m), n)) else return Nothing
              _ -> return Nothing
    a' <- resolveANF a
    case a'^.val of
      AEApp (PRes (PDot PTop "dh_combine")) _ [x, y] -> do
          tx <- inferAExpr x
          xpub <- tyFlowsTo tx advLbl
          xwf <- decideProp $ pEq (builtinFunc "is_group_elem" [x]) (builtinFunc "true" [])
          ty <- inferAExpr y
          case extractNameFromType ty of
            Just ny -> do
                ny_local <- nameExpIsLocal ny
                nty <- getNameType ny
                case nty^.val of
                  NT_DH -> 
                      if (xwf == Just True) && xpub && ny_local then return (Just (x, ny)) else go_from_ty
                  _ -> return Nothing
            _ -> go_from_ty
      _ -> go_from_ty

inferKDFODH :: (AExpr, Ty) -> (AExpr, Ty) -> (AExpr, Ty) -> String -> ([Idx], [Idx]) -> KDFSelector -> Int -> Check (Maybe KDFInferResult) 
inferKDFODH a (b, tb) c s ips i j = do
    pth <- curModName
    (ne1, ne2, p, str_nts) <- getODHNameInfo (PRes (PDot pth s)) ips (fst a) (fst c) i j
    let (str, nt) = str_nts !! j
    let dhCombine x y = mkSpanned $ AEApp (topLevelPath "dh_combine") [] [x, y]
    let dhpk x = mkSpanned $ AEApp (topLevelPath "dhpk") [] [x]
    res <- do
        let real_ss = dhCombine (dhpk (mkSpanned $ AEGet ne1)) (mkSpanned $ AEGet ne2)
        beq <- decideProp $ pEq b real_ss
        case beq of 
          Just True -> do
              b2 <- decideProp p
              b3 <- flowsTo (nameLbl ne1) advLbl
              b4 <- flowsTo (nameLbl ne2) advLbl
              if (b2 == Just True) then 
                    if (not b3) && (not b4) then
                        return $ Just $ KDFGood str $
                            mkSpanned $ ODHName (PRes (PDot pth s)) ips (fst a) (fst c) i j
                    else do
                        l_corr <- coveringLabelOf [snd a, snd c]
                        return $ Just $ KDFCorrupt (joinLbl advLbl l_corr) str_nts
              else return Nothing
          _ -> return Nothing
    res2 <- case res of
        Just v@(KDFGood _ _) -> return $ Just v
        _ -> do 
            oxy <- getLocalDHComputation b
            case oxy of
              Just (x, ny) -> do
                -- h(a, g^xy, c) is public when:
                --    (a, g^xy, c) not in ODH
                --    the DH computation is local (involves a module-local DH name)
                --    one of the x,y is secret
                (_, notODH) <- SMT.smtTypingQuery "" $ SMT.symAssert $ pNot $ mkSpanned $ PInODH (fst a) b (fst c) 
                case notODH of
                  False -> return Nothing
                  True -> do
                      ny_sec <- not <$> flowsTo (nameLbl ny) advLbl
                      if ny_sec then return (Just KDFAdv) else do
                         tx <- inferAExpr x
                         case tx^.val of
                           TDH_PK nx -> do
                               nx_sec <- not <$> flowsTo (nameLbl nx) advLbl
                               if nx_sec then return (Just KDFAdv) else return Nothing
                           _ -> return Nothing
              Nothing -> return Nothing
    case res2 of
      Nothing -> return res -- here, res is either Nothing or KDFCorrupt
      Just _ -> return res2


nameKindLength :: NameKind -> AExpr
nameKindLength nk =
    aeLenConst $ case nk of
                               NK_KDF -> "kdfkey"
                               NK_DH -> "dhkey"
                               NK_Enc -> "enckey"
                               NK_PKE -> "pkekey"
                               NK_Sig -> "sigkey"
                               NK_MAC -> "mackey"
                               NK_Nonce -> "nonce"


checkCryptoOp :: CryptOp -> [(AExpr, Ty)] -> Check Ty
checkCryptoOp cop args = pushRoutine ("checkCryptoOp(" ++ show (owlpretty cop) ++ ")") $ do
    tcs <- view tcScope
    case (tcs, cop) of
      (TcGhost b, CLemma _) -> assert ("Lemma " ++ show (owlpretty cop) ++ " cannot be called here") b
      (TcGhost _, _) -> typeError $ "Crypto op " ++ show (owlpretty cop) ++ " cannot be executed in ghost"
      _ -> return ()
    case cop of
      CLemma (LemmaKDFInj nks j) -> typeError "unimp"
      CLemma (LemmaCRH) -> local (set tcScope $ TcGhost False) $ do 
          assert ("crh_lemma takes two arguments") $ length args == 2
          let [(x, _), (y, _)] = args
          x' <- resolveANF x
          y' <- resolveANF y
          return $ tRefined tUnit "._" $
              pImpl
                (pEq (aeApp (topLevelPath "crh") [] [x])
                     (aeApp (topLevelPath "crh") [] [y]))
                (pEq x y)
      CLemma (LemmaDisjNotEq) -> do
          assert ("disjoint_not_eq_lemma takes two arguments") $ length args == 2
          let [(x, _), (y, _)] = args
          x' <- normalizeAExpr =<< resolveANF x
          y' <- normalizeAExpr =<< resolveANF y
          proveDisjointContents x' y'
          return $ tRefined tUnit "._" $ pNot $ pEq x' y'
      CLemma (LemmaCrossDH n) -> do
          -- Below states that, given g^x, y, and z, it is hard to construct h such that h^x = g^(y * z)
          assert ("Wrong number of arguments to cross_dh_lemma") $ length args == 1
          let [(x, t)] = args
          b <- tyFlowsTo t advLbl
          assert ("Argument to cross_dh_lemma must flow to adv") b
          nt <- getNameType n
          assert ("Name parameter to cross_dh_lemma must be a DH name") $ (nt^.val) `aeq` NT_DH
          odhs <- view $ curMod . odh
          let dhCombine x y = mkSpanned $ AEApp (topLevelPath "dh_combine") [] [x, y]
          let dhpk x = mkSpanned $ AEApp (topLevelPath "dhpk") [] [x]
          let pSec m = pNot $ pFlow (nameLbl m) advLbl
          ps <- forM odhs $ \(_, b) -> do
              ((is, ps), (n2, n3, _)) <- unbind b
              p <- withIndices (map (\i -> (i, IdxSession)) is ++ map (\i -> (i, IdxPId)) ps) $ do
                  n_disj <- liftM2 pAnd (pNot <$> pNameExpEq n n2) (pNot <$> pNameExpEq n n3)
                  return $ pImpl (n_disj `pAnd` (pSec n))
                                        (pNot $ pEq (dhCombine x $ aeGet n)
                                                    (dhCombine (dhpk $ aeGet n2) (aeGet n3)))
              return $ mkForallIdx (is ++ ps) p
          p <- normalizeProp $ (foldr pAnd pTrue ps) 
          return $ tLemma p
      CLemma (LemmaConstant)  -> do
          assert ("Wrong number of arguments to is_constant_lemma") $ length args == 1
          let [(x, _)] = args
          x' <- resolveANF x
          x'' <- normalizeAExpr x'
          let b = isConstant x''
          assert ("Argument is not a constant: " ++ show (owlpretty x'')) b
          return $ tRefined tUnit "._" $ mkSpanned $ PIsConstant x''
      CKDF oann1 oann2 nks j -> do
          assert ("KDF must take three arguments") $ length args == 3
          let [a, b, c] = args
          cpub <- tyFlowsTo (snd c) advLbl
          assert ("Third argument to KDF must flow to adv") cpub
          res1 <- do
              let go os = 
                      case os of
                        [] -> do
                            pub <- tyFlowsTo (snd a) advLbl
                            assert ("No KDF hints worked for first argument; salt must then flow to adv") pub
                            return Nothing
                        i:os' -> do
                            r <- local (set tcScope $ TcGhost False) $ inferKDF KDF_SaltPos a b c i j nks
                            case r of
                              Just v -> return $ Just (i, v)
                              Nothing ->  go os'
              go oann1
          res2 <- do
              let go os =
                      case os of
                        [] -> do
                            pub <- tyFlowsTo (snd b) advLbl
                            assert ("No KDF hints worked for second argument; IKM must then flow to adv") pub
                            return Nothing
                        e:os' -> do
                            r <- case e of
                                   Left i -> local (set tcScope $ TcGhost False) $ inferKDF KDF_IKMPos a b c i j nks
                                   Right (s, ps, i) -> local (set tcScope $ TcGhost False) $ inferKDFODH a b c s ps i j
                            case r of
                              Just v -> return $ Just (e, v)
                              Nothing -> go os'
              go oann2
          res <- case (res1, res2) of
                   (Nothing, Just (e, v)) -> return $ Just v
                   (Just (i, v), Nothing) -> return $ Just v
                   (Nothing, Nothing) -> return Nothing
                   (Just (i, v1), Just (e, v2)) -> do
                       v <- pushRoutine "KDF.unify" $ local (set tcScope $ TcGhost False) $ unifyKDFInferResult i e v1 v2
                       return $ Just v
          assert ("Name kind index out of bounds") $ j < length nks
          let outLen = nameKindLength $ nks !! j
          kdfProp <- do
              a' <- resolveANF (fst a)
              b' <- resolveANF (fst b)
              c' <- resolveANF (fst c)
              return $ pEq (aeVar ".res") $ mkSpanned $ AEKDF a' b' c' nks j 
          let kdfRefinement t = tRefined t ".res" $ 
                pAnd
                    (pEq (aeLength (aeVar ".res")) outLen)
                    kdfProp
          kdfRefinement <$> case res of 
            Nothing -> mkSpanned <$> trivialTypeOf [snd a, snd b, snd c] 
            Just KDFAdv -> return $ tData advLbl advLbl
            Just (KDFGood strictness ne) -> pushRoutine "KDF.good" $ do 
              let flowAx = case strictness of
                             KDFStrict -> pNot $ pFlow (nameLbl ne) advLbl -- Justified since one of the keys must be secret
                             KDFUnstrict -> pTrue
              lenConst <- local (set tcScope $ TcGhost False) $ lenConstOfUniformName ne
              return $ mkSpanned $ TRefined (tName ne) ".res" $ bind (s2n ".res") $ 
                  pAnd flowAx $ 
                      pEq (aeLength (aeVar ".res")) lenConst
            Just (KDFCorrupt l_corr nts) -> pushRoutine "KDF.corrupt" $ do 
                p <- local (set tcScope $ TcGhost False) $ corruptKDFChain nts >>= normalizeProp
                let args_public = pFlow l_corr advLbl
                let ot = tDataAnn l_corr zeroLbl "public KDF"
                return $ tRefined ot "._" $ pImpl args_public p
      CAEnc -> do
          assert ("Wrong number of arguments to encryption") $ length args == 2
          let [(_, t1), (x, t)] = args
          doAEnc t1 x t args
      CADec -> do 
          assert ("Wrong number of arguments to decryption") $ length args == 2
          let [(_, t1), (_, t)] = args
          doADec t1 t args
      CEncStAEAD p iargs -> do
          checkCounterIsLocal p iargs
          assert ("Wrong number of arguments to stateful AEAD encryption") $ length args == 3
          let [(_, t1), (x, t), (y, t2)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf (map snd args)
            Just k -> do
                nt <- local (set tcScope $ TcGhost False) $ getNameType k
                case nt^.val of
                  NT_StAEAD tm xaad p' -> do
                      pnorm <- normalizePath p
                      pnorm' <- normalizePath p'
                      assert ("Wrong counter for AEAD: expected " ++ show (owlpretty p') ++ " but got " ++ show (owlpretty p)) $ pnorm `aeq` pnorm'
                      b1 <- isSubtype t tm
                      (xa, aadp) <- unbind xaad
                      b2 <- isSubtype t2 $ tRefined (tData advLbl advLbl) ".res" $
                          pImpl (pNot $ pFlow (nameLbl k) advLbl)
                                (subst xa (aeVar ".res") aadp)
                      if b1 && b2 then return $ tRefined (tData advLbl advLbl) ".res" $ pEq (aeLength (aeVar ".res")) (aeApp (topLevelPath $ "cipherlen") [] [aeLength x])
                                  else mkSpanned <$> trivialTypeOf (map snd args)
                  _ -> mkSpanned <$> trivialTypeOf (map snd args)
      CDecStAEAD -> do
          assert ("Wrong number of arguments to stateful AEAD decryption") $ length args == 4
          let [(_, t1), (x, t), (y, t2), (_, tnonce)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf (map snd args)
            Just k -> do
                nt <- local (set tcScope $ TcGhost False) $ getNameType k
                case nt^.val of
                  NT_StAEAD tm xaad _ -> do
                      b1 <- flowsTo (nameLbl k) advLbl
                      b2 <- tyFlowsTo tnonce advLbl
                      b3 <- tyFlowsTo t advLbl
                      b4 <- tyFlowsTo t2 advLbl
                      if (not b1) && b2 && b3 && b4 then do
                            (x, aad) <- unbind xaad
                            return $ mkSpanned $ TOption $ tRefined tm ".res" $ subst x y aad
                      else if (b1 && b2 && b3 && b4) then do 
                          return $ mkSpanned $ TOption $ tDataAnn advLbl advLbl "corrupt dec"
                      else (mkSpanned <$> trivialTypeOf (map snd args))
                  _ -> do
                      l <- coveringLabelOf [t1, t, t2, tnonce]
                      b <- flowsTo l advLbl
                      if b then 
                        return $ mkSpanned $ TOption $ tDataAnn advLbl advLbl "corrupt dec"
                      else 
                          return $ tDataAnn l l "corrupt dec"
      CPKDec -> do 
          assert ("Wrong number of arguments to pk decryption") $ length args == 2
          let [(_, t1), (_, t)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just k -> do
              nt <- local (set tcScope $ TcGhost False) $  getNameType k
              case nt^.val of
                NT_PKE t' -> do
                    l <- coveringLabel t
                    b1 <- flowsTo l advLbl
                    b2 <- flowsTo (nameLbl k) advLbl
                    if b1 && (not b2) then do
                        -- TODO: is this complete?
                        return $ mkSpanned $ TOption $ mkSpanned $ TUnion t' $ tDataAnn advLbl advLbl "adversarial message"
                    else if b1 && b2 then do 
                        let l_corr = joinLbl (nameLbl k) l
                        return $ mkSpanned $ TOption $ tDataAnn advLbl advLbl "corrupt pkdec"
                    else mkSpanned <$> trivialTypeOf [t1, t]
      CPKEnc -> do 
          assert ("Wrong number of arguments to pk encryption") $ length args == 2
          let [(_, t1), (x, t)] = args
          case extractEncPKFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just k -> do
                nt <- local (set tcScope $ TcGhost False) $  getNameType k
                case nt^.val of
                  NT_PKE t' -> do
                      b <- isSubtype t t'
                      if (b) then
                          return $ mkSpanned $ TRefined (tData advLbl advLbl) ".res" $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (aeApp (topLevelPath $ "pk_cipherlen") [] [aeLength x])
                      else
                          mkSpanned <$> trivialTypeOf [t1, t] 
                  _ -> typeError $ show $ ErrWrongNameType k "encryption key" nt
      CMac -> do
          assert ("Wrong number of arguments to mac") $ length args == 2
          let [(_, t1), (_, t)] = args
          let withMacLength t = 
                  tRefined t ".res" $ pEq (aeLength (aeVar ".res")) (aeLenConst "maclen")
          withMacLength <$> case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just k -> do 
                nt <-  local (set tcScope $ TcGhost False) $ getNameType k
                case nt^.val of
                  NT_MAC t' -> do
                      assertSubtype t t'
                      l <- coveringLabel t'
                      return $ tData l advLbl 
                  _ -> mkSpanned <$> trivialTypeOf [t1, t]
      CMacVrfy -> do
          assert ("Wrong number of arguments to mac_vrfy") $ length args == 3
          let [(xt1, t1), (m, mt), (xt, t)] = args
          case extractNameFromType t1 of
            Nothing -> do
                l <- coveringLabelOf [t1, mt, t] 
                b <- flowsTo l advLbl
                if b then 
                    return $ mkSpanned $ TOption $ tDataAnn advLbl advLbl "corrupt mac"
                else return $ tData l l
            Just k -> do
                nt <- local (set tcScope $ TcGhost False) $ getNameType k
                case nt^.val of
                  NT_MAC t' -> do
                      l1 <- coveringLabel mt
                      l2 <- coveringLabel t
                      b1 <- flowsTo  l1 advLbl
                      b2 <- flowsTo  l2 advLbl
                      b3 <- flowsTo  (nameLbl k) advLbl
                      if (b1 && b2 && (not b3)) then
                        return $ mkSpanned $ TOption (tRefined t' ".res" $ (pEq (aeVar ".res") m))
                      else if (b1 && b2 && b3) then 
                        return $ mkSpanned $ TOption $ mkSpanned $ (TData advLbl advLbl (ignore $ Just "corrupt mac")) -- Change here
                      else
                        let l_corr = joinLbl (nameLbl k) (joinLbl l1 l2) in
                        return $ mkSpanned $ (TData l_corr l_corr (ignore $ Just "corrupt mac")) -- Change here
      CSign -> do
          assert ("Wrong number of arguments to sign") $ length args == 2
          let [(_, t1), (_, t)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just sk -> do
                nt <- local (set tcScope $ TcGhost False) $  getNameType sk
                case nt^.val of
                  NT_Sig t' -> do
                      assertSubtype t t'
                      l <- coveringLabel t'
                      return $ mkSpanned $ TRefined (tData l advLbl) ".res" $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (mkSpanned $ AELenConst "signature")
                  _ -> mkSpanned <$> trivialTypeOf [t1, t]
      CSigVrfy -> do
          assert ("Wrong number of arguments to vrfy") $ length args == 3
          let [(_, t1), (_, t2), (_, t3)] = args
          case extractVKFromType t1 of
            Nothing -> do
                l <- coveringLabelOf [t1, t2, t3]
                b <- flowsTo l advLbl
                if b then 
                    return $ mkSpanned $ TOption $ mkSpanned $ TData advLbl advLbl (ignore $ Just $ "corrupt vrfy") 
                else 
                    return $ mkSpanned $ TData l l (ignore $ Just $ "corrupt vrfy") 
            Just k -> do 
                nt <-  local (set tcScope $ TcGhost False) $ getNameType k
                case nt^.val of
                  NT_Sig t' -> do
                      l <- coveringLabel t'
                      let l' = joinLbl l advLbl
                      b1 <- tyFlowsTo t2 l'
                      b2 <- tyFlowsTo t3 l'
                      b3 <- flowsTo (nameLbl k) advLbl
                      if (b1 && b2 && (not b3)) then return (mkSpanned $ TOption t')
                      else do
                          b1' <- tyFlowsTo t2 advLbl
                          b2' <- tyFlowsTo t3 advLbl
                          if (b1' && b2' && b3) then return $ mkSpanned $ TOption $ mkSpanned $ TData advLbl advLbl (ignore $ Just "corrupt vrfy")
                          else do
                             l_corr <- coveringLabelOf [t1, t2, t3]
                             return $ mkSpanned $ (TData l_corr l_corr $ ignore $ Just "corrupt vrfy") 
                  _ -> typeError $ show $ ErrWrongNameType k "sig" nt

---- Entry point ----

typeCheckDecls :: Flags -> [Decl] -> IO (Either Env Env)
typeCheckDecls f ds = do
    e <- emptyEnv f
    r <- PR.runResolve f $ PR.resolveDecls ds
    case r of
      Left () -> return $ Left e
      Right ds' -> do
          runExceptT $ runReaderT (unCheck $ do
              loadSMTCache
              checkDeclsWithCont ds' $ do
                  writeSMTCache
                  ask) e


---- Module stuff ----


defMatches :: String -> Maybe Def -> Def -> Check ()
defMatches s d1 d2 = 
    case (d1, d2) of
      (Just (DefHeader bl), DefHeader bl') -> assert ("Def mismatch with headers: " ++ s) $ bl `aeq` bl'
      (Just (DefHeader bl), Def blspec) -> do
          (is, DefSpec _ l _) <- unbind blspec
          assert ("Def mismatch: " ++ s) $ bl `aeq` (bind is l)
      (Just (Def blspec), Def blspec') -> do
          (is1, DefSpec ab l1 pty) <- unbind blspec
          (is', DefSpec ab' l1' pty') <- unbind blspec'
          assert ("Def abstractness mismatch: " ++ s) $ (not (unignore ab)) || (unignore ab') -- ab ==> ab'
          assert ("Def locality mismatch") $ (bind is1 l1) `aeq` (bind is' l1')
          prereq_retty1 <- withDepBind pty $ \_ (x, y, _) -> return (x, y)
          prereq_retty2 <- withDepBind pty' $ \_ (x, y, _) -> return (x, y)
          assert ("Def mismatch on prereq or return ty") $ (bind is1 prereq_retty1) `aeq` (bind is' prereq_retty2)
      (Nothing, _) -> typeError $ "Missing def: " ++ s

tyDefMatches :: String -> TyDef -> TyDef -> Check ()
tyDefMatches s td1 td2 = 
    case (td1, td2) of
      (EnumDef d1, EnumDef d2) -> assert ("Enum mismatch: " ++ s) $ d1 `aeq` d2
      (StructDef d1, StructDef d2) -> assert ("Struct mismatch: " ++ s) $ d1 `aeq` d2
      _ -> typeError $ "UNIMP: tyDefMatches"


userFuncMatches :: String -> UserFunc -> UserFunc -> Check ()
userFuncMatches s f1 f2 = assert ("Func mismatch: " ++ s) $ f1 `aeq` f2

nameDefMatches :: String -> 
    Bind ([IdxVar], [IdxVar]) NameDef -> 
    Bind ([IdxVar], [IdxVar]) NameDef -> 
    Check ()
nameDefMatches s xn1 xn2 = do
    ((is1, is2), on1) <- unbind xn1
    ((is1', is2'), on2) <- unbind xn2
    case (substs (zip is1 (map mkIVar is1')) $ substs (zip is2 (map mkIVar is2')) $ on1, on2) of
      (_, AbstractName) -> assert ("Arity mismatch for " ++ s) $ (length is1 == length is1') && (length is2 == length is2')
      (AbstractName, _) -> typeError $ "Name should be concrete: " ++ show s
      (BaseDef (nt1, ls1), BaseDef (nt2, ls2)) -> do
          assert ("Name type mismatch on name " ++ s) $ nt1 `aeq` nt2
          assert ("Locality mismatch on name " ++ s) $ ls1 `aeq` ls2
      _ -> error "unimp: nameDefMatches"

moduleMatches :: ModDef -> ModDef -> Check ()
moduleMatches md1 md2 = 
    case (md1, md2) of 
      (MAlias p, _) -> do
          d <- getModDef p
          moduleMatches d md2
      (_, MAlias p) -> do
          d <- getModDef p
          moduleMatches md1 d 
      (MBody _, MFun _ _ _) -> typeError $ "Expected functor, but got module"
      (MFun _ _ _, MBody _) -> typeError $ "Expected module, but got functor"
      (MFun s t1 xmd1, MFun _ t2 ymd2) -> do
          moduleMatches t2 t1
          (x, md1) <- unbind xmd1
          (y, md2_) <- unbind ymd2
          let md2 = subst y (PPathVar (ClosedPathVar $ ignore $ show x) x) md2_
          p <- curModName
          local (over modContext $ insert x t1) $ 
                moduleMatches md1 md2
      (MBody xmd1, MBody ymd2) -> do
          (x, md1) <- unbind xmd1
          (y, md2_) <- unbind ymd2
          let md2 = subst y (PPathVar OpenPathVar x) md2_
          -- Localities
          forM_ (md2^.localities) $ \(s, i) -> do
              ar1 <- case i of
                       Left ar -> return ar
                       Right p -> normLocalityPath $ PRes p 
              ar2 <- case lookup s (md1^.localities) of
                       Nothing -> typeError $ "Locality not found for module match: " ++ s
                       Just (Left ar) -> return ar
                       Just (Right p) -> normLocalityPath $ PRes p
              assert ("Locality arity mismatch for module match: " ++ s) $ ar1 == ar2
          -- Defs
          forM_ (md2^.defs) $ \(s, df) -> defMatches s (lookup s (md1^.defs)) df
          -- TableEnv
          forM_ (md2^.tableEnv) $ \(s, tl) -> 
              case lookup s (md1^.tableEnv) of
                Nothing -> typeError $ "Missing tenv: " ++ s
                Just tl' -> assert ("Table mismatch for " ++ s) $ tl `aeq` tl'
          -- flowAxioms 
          forM_ (md2^.flowAxioms) $ \ax -> 
              case L.find (aeq ax) (md1^.flowAxioms) of 
                Nothing -> typeError $ "flow axiom mismatch " ++ show (owlpretty ax)
                Just _ -> return ()
          -- advCorrConstraints 
          forM_ (md2^.advCorrConstraints) $ \ax -> 
              case L.find (aeq ax) (md1^.advCorrConstraints) of 
                Nothing -> do
                    let (is, ps) = owlprettyBind ax
                    typeError $ "corr constraint mismatch: " ++ show ps
                Just _ -> return ()
          -- tyDefs 
          forM_ (md2^.tyDefs) $ \(s, td) -> 
              case lookup s (md1^.tyDefs) of
                Nothing -> typeError $ "Type missing: " ++ s
                Just td' -> tyDefMatches s td' td
          -- userFuncs
          forM_ (md2^.userFuncs) $ \(s, f) -> 
              case lookup s (md1^.userFuncs) of
                Nothing -> typeError $ "Func missing: " ++ s
                Just f' -> userFuncMatches s f' f
          -- nameEnv
          forM_ (md2^.nameDefs) $ \(s, n) -> 
              case lookup s (md1^.nameDefs) of 
                Nothing -> typeError $ "Name missing: " ++ s
                Just n' -> nameDefMatches s n' n
          -- modules
          forM_ (md2^.modules) $ \(s, m1) ->
              case lookup s (md1^.modules) of
                Nothing -> typeError $ "Module missing: " ++ s
                Just m2 -> moduleMatches m2 m1 

--moduleMatches :: Bind (Name ResolvedPath) ModDef -> Bind (Name ResolvedPath) ModDef -> Check ()
--moduleMatches xmd1 ymd2 = do

typeError' :: String -> Check a
typeError' msg = do
    pos <- view curSpan
    fn <- S.takeFileName <$> (view $ envFlags . fFilePath)
    fl <- S.takeDirectory <$> (view $ envFlags . fFilePath)
    f <- view $ envFlags . fFileContents
    ite <- view inTypeError
    info <- case ite of
              True -> return []
              False -> do
                (_, b) <- local (set inTypeError True) $ SMT.smtTypingQuery "typeError false check" $ SMT.symAssert $ mkSpanned PFalse
                return $ if b then [E.Note "Inconsistent type context detected. Try using false_elim?"] else []
    tyc <- removeAnfVars <$> view tyContext 
    let rep = E.Err Nothing msg [(pos, E.This msg)] info
    let diag = E.addFile (E.addReport def rep) (fn) f  
    e <- ask
    E.printDiagnostic S.stdout True True 4 E.defaultStyle diag 
    liftIO $ putDoc $ owlpretty "Type context" <> line <> pretty "===================" <> line <> owlprettyTyContext tyc <> line
    writeSMTCache
    -- Uncomment for debugging
    -- rs <- view tcRoutineStack
    -- logTypecheck $ owlpretty "Routines: " <> (mconcat $ L.intersperse (owlpretty ", ") $ map owlpretty rs)
    -- inds <- view inScopeIndices
    -- logTypecheck $ "Indices: " ++ show (owlprettyIndices inds)
    Check $ lift $ throwError e
