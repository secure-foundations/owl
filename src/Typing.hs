{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
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

emptyModBody :: IsModuleType -> ModBody
emptyModBody t = ModBody t mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty 

-- extend with new parts of Env -- ok
emptyEnv :: Flags -> IO Env
emptyEnv f = do
    r <- newIORef 0
    r' <- newIORef 0
    r'' <- newIORef 0
    m <- newIORef $ M.empty
    rs <- newIORef []
    return $ Env f initDetFuncs mempty TcGhost mempty mempty [(Nothing, emptyModBody ModConcrete)] mempty 
        interpUserFunc r m mempty rs r' r'' (typeError') Nothing def


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
              b <- isSubtype t1 t
              l <- coveringLabel t1
              if b then return (TOption t) else return (TData l l $ ignore (Just $ "error on Some")) 
          _ -> typeError $ show $ ErrBadArgs "Some" (map snd args))),
    ("None", (0, \ps args -> do
        case (ps, args) of
          ([ParamTy t], []) -> do
              return (TOption t)
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
    mkSimpleFunc "is_group_elem" 1 $ \args -> trivialTypeOf args,
    mkSimpleFunc "concat" 2 $ \args -> trivialTypeOf args, -- Used for RO
    mkSimpleFunc "cipherlen" 1 $ \args -> trivialTypeOf args,
    mkSimpleFunc "pk_cipherlen" 1 $ \args -> trivialTypeOf args,
    mkSimpleFunc "vk" 1 $ \args ->
        case args of
          [t] | Just n <- extractNameFromType t -> do
              nt <- local (set tcScope TcGhost) $ getNameType n
              case nt^.val of
                NT_Sig _ ->
                    return $ TRefined (mkSpanned $ TVK n) ".res" $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (mkSpanned $ AELenConst "vk")
                _ -> trivialTypeOf args
          _ -> trivialTypeOf args,
    mkSimpleFunc "dhpk" 1 $ \args ->
        case args of
          [t] | Just n <- extractNameFromType t -> do
              nt <- local (set tcScope TcGhost) $ getNameType n
              case nt^.val of
                NT_DH -> return $ TDH_PK n
                _ -> trivialTypeOf args
          _ -> trivialTypeOf args,
    mkSimpleFunc "enc_pk" 1 $ \args ->
        case args of
          [t] | Just n <- extractNameFromType t -> do
              nt <-  local (set tcScope TcGhost) $ getNameType n
              case nt^.val of
                NT_PKE _ -> return $ TEnc_PK n
                _ -> trivialTypeOf args
          _ -> trivialTypeOf args,
    ("dh_combine", (2, \ps args ->
        case (ps, args) of
          ([], [(_, t1), (_, t2)]) | Just n <- extractDHPKFromType t1, Just m <- extractNameFromType t2 -> do
              nt_n <-  local (set tcScope TcGhost) $ getNameType n
              nt_m <-  local (set tcScope TcGhost) $ getNameType m
              case (nt_n^.val, nt_m^.val) of
                (NT_DH, NT_DH) -> return $ TSS n m
                _ -> trivialTypeOf $ map snd args
          ([], _) -> trivialTypeOf $ map snd args
          ([ParamName n, ParamName m], [(x, t1), (_, t2)]) -> do 
              nt_n <-  local (set tcScope TcGhost) $ getNameType n
              nt_m <-  local (set tcScope TcGhost) $ getNameType m
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
                  debug $ owlpretty "Checking name " <> owlpretty n <> owlpretty " against " <> owlpretty m
                  if n `aeq` m then return $ TRefined (mkSpanned $ TBool zeroLbl) ".res" (bind (s2n ".res") (pEq (aeVar ".res") (aeApp (topLevelPath $ "true") [] [])))
                  else case (n^.val, m^.val) of
                       (NameConst (is1, is1') a oi1, NameConst (is2, is2') b oi2) | (a, oi1) `aeq` (b, oi2) -> do
                           let p =  foldr pAnd pTrue $ map (\(i, j) -> mkSpanned $ PEqIdx i j) $ zip (is1 ++ is1') (is2  ++ is2')
                           return $ TRefined (mkSpanned $ TBool advLbl) ".res" (bind (s2n ".res") (pImpl (pEq (aeVar ".res") (aeApp (topLevelPath $ "true") [] [])) p))
                       _ -> do
                           l <- coveringLabelOf $ map snd args
                           return $ TBool l
                (TName n, m) -> do
                  nt <-  local (set tcScope TcGhost) $ getNameType n
                  case nt^.val of
                    NT_Nonce -> do
                        l <- coveringLabel (mkSpanned m)
                        return $ TRefined (mkSpanned $ TBool l) ".res" (bind (s2n ".res") (pImpl (pEq (aeVar ".res") (aeApp (topLevelPath $ "true") [] [])) (pAnd (pFlow (nameLbl n) l) (pEq x y))))
                    _ -> trivialTypeOf $ map snd args
                (m, TName n) -> do
                  nt <-  local (set tcScope TcGhost) $ getNameType n
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

mkStructType :: ResolvedPath -> TyVar -> [FuncParam] -> [AExpr] -> [(String, Ty)] -> Check TyX
mkStructType pth tv ps xs fields = do
    etaRules <- forM [0 .. (length fields - 1)] $ \i -> 
        return $ pEq (xs !! i) $ mkSpanned $ AEApp (PRes $ PDot pth (fst $ fields !! i)) ps [aeVar ".res"]
    let etaRule = foldr pAnd pTrue etaRules
    return $ TRefined (mkSpanned $ TConst (PRes $ PDot pth tv) ps) ".res" $
            bind (s2n ".res") $ 
                pAnd (pEq (aeLength (aeVar ".res")) (sumOfLengths xs))
                     etaRule


        

interpUserFunc :: ResolvedPath -> ModBody -> UserFunc -> Check (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX)
interpUserFunc pth md (StructConstructor tv) = do
    case lookup tv (md^.tyDefs) of
      Just (StructDef idf) -> do
          let (is_ar, ar) = let (xs, ys) = unsafeUnbind idf in (length xs, length ys)
          return (ar, \ps xs -> do
              forM_ ps checkParam
              nts <- extractStruct ps (show tv) idf 
              assert (show $ owlpretty "Index arity mismatch on struct constructor") $ length ps == is_ar 
              if length xs == ar then do
                b <- foldM (\acc i -> do
                    b1 <- isSubtype (snd $ xs !! i) (snd $ nts !! i) 
                    return $ acc && b1) True [0..(length xs - 1)]
                if b then mkStructType pth tv ps (map fst xs) nts else trivialTypeOf (map snd xs)
              else trivialTypeOf (map snd xs))
      _ -> typeError $ "Unknown struct: " ++ show tv
interpUserFunc pth md (StructProjector tv field) = do
    case lookup tv (md^.tyDefs) of
      Just (StructDef idf) -> do
          let (is_ar, ar) = let (xs, ys) = unsafeUnbind idf in (length xs, length ys)
          return (1, \ps args -> do
              forM_ ps checkParam
              nts <- extractStruct ps (show tv) idf 
              assert (show $ owlpretty "Index arity mismatch on struct constructor") $ length ps == is_ar 
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



-- Normalize a type expression. Only nontrivial computations are to normalize a
-- nested refinement, and to normalize a case whether a name n is honest.
normalizeTy :: Ty -> Check Ty
normalizeTy t0 = local (set tcScope TcGhost) $ do
    debug $ owlpretty "normalizeTy: " <> owlpretty t0
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
            p' <- withVars [(x, (ignore $ show x, Nothing, t'))] $ simplifyProp p
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
            debug $ owlpretty "Normalizing " <> owlpretty t0
            (x, t) <- unbind xt
            if x `elem` getTyIdxVars t then do
                t' <- local (over (inScopeIndices) $ insert x IdxGhost) $ normalizeTy t
                return $ Spanned (t0^.spanOf) $ TExistsIdx $ bind x t'
            else normalizeTy t
        TAdmit -> return t0

normalizeLabel :: Label -> Check Label
normalizeLabel l = do                
    debug $ owlpretty "Normalizing " <> owlpretty l
    normLabel l



-- Subtype checking, assuming the types are normalized

isSubtype' t1 t2 = do
    case (t1^.val, t2^.val) of
      _ | isSingleton t2 -> do 
          debug $ owlpretty "Trying singleton query: " <> owlpretty t2
          (_, b) <- SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2
          debug $ owlpretty "Singleton query: " <> owlpretty t1 <> owlpretty "<=" <> owlpretty t2 <> owlpretty ": " <> owlpretty b
          return b 
      (TCase p t1' t2', _) -> do
          debug $ owlpretty "Checking subtype for TCase: " <> owlpretty t1 <> owlpretty " <= " <> owlpretty t2
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
      (TRefined t1' s1 p1, TRefined t2' s2 p2) -> do
        b1 <- isSubtype' t1' t2'
        (_, b) <- SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2
        return $ b1 && b
      (TUnit, TRefined (Spanned _ TUnit) _ p) -> do
        x' <- freshVar
        isSubtype' (tRefined tUnit "_x" pTrue)  t2
      (TRefined t _ _, t') | (t^.val) `aeq` t' -> return True
      (_, TRefined t _ p) -> do
          b1 <- isSubtype' t1 t
          (_, b2) <- SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2
          return $ b1 && b2
      (_, TUnit) -> snd <$> (SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2)
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
          debug $ owlpretty "Alpha equivalence between TConsts: " <> owlpretty (aeq x' y')
          case (aeq x' y', td) of
            (True, EnumDef _) -> return $ aeq ps1 ps2 
            (True, StructDef _) -> do
                assert (show $ owlpretty "Func param arity mismatch on struct") $ length ps1 == length ps2
                qs <- forM (zip ps1 ps2) $ \(p1, p2) ->
                    case (p1, p2) of
                      (ParamIdx i1, ParamIdx i2) -> return $ mkSpanned $ PEqIdx i1 i2
                      _ -> typeError $ "Bad param to struct: didn't get index"
                let p = foldr pAnd pTrue qs
                (_, b) <- SMT.smtTypingQuery $ SMT.symAssert p
                return b
            _ -> return False
      (TSS n m, TSS m' n') | (n `aeq` n') && (m `aeq` m') -> return True -- TODO maybe all we want? not sure
      (TExistsIdx xt1, TExistsIdx xt2) -> do
          (xi, t1) <- unbind xt1
          (xi', t2) <- unbind xt2
          local (over (inScopeIndices) $ insert xi IdxGhost) $
              isSubtype' t1 (subst xi' (mkIVar xi) t2)
      (_, TUnion t1' t2') -> do
          b1 <- isSubtype' t1 t1'
          b2 <- isSubtype' t1 t2'
          return $ b1 || b2
      (t, TDataWithLength l a) -> do
          debug $ owlpretty "Checking TDataWithLength with " <> owlpretty t1 <> owlpretty " <= " <> owlpretty t2
          b1 <- isSubtype' t1 (tData l l)
          (_, b) <- SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2
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
    debug $ owlpretty (unignore $ t1^.spanOf) <> owlpretty (unignore $ t2^.spanOf) <> owlpretty "Checking subtype of " <> owlpretty t1 <> owlpretty " and " <> owlpretty t2
    t1' <- normalizeTy t1
    t2' <- normalizeTy t2
    b <- isSubtype' t1' t2'
    debug $ owlpretty "Subtype of " <> owlpretty t1 <> owlpretty " and " <> owlpretty t2 <> owlpretty ": " <> owlpretty b
    return b



assertSubtype :: Ty -> Ty -> Check ()
assertSubtype t1 t2 = laxAssertion $ do
    tyc <- view tyContext
    debug $ owlpretty "Asserting subtype " <> owlpretty t1 <> owlpretty " <= " <> owlpretty t2 <> owlpretty "Under context: " <> owlprettyTyContext tyc
    b <- isSubtype t1 t2
    t1' <- normalizeTy t1
    t2' <- normalizeTy t2
    assert (show $ ErrCannotProveSubtype t1' t2') b

typeProtectsLabel' :: Label -> Ty -> Check ()
typeProtectsLabel' l t0 =
    laxAssertion $ case t0^.val of
      (TData l' _ _) -> flowCheck l l'
      (TDataWithLength l' _) -> flowCheck l l'
      (TOption t) -> flowCheck l advLbl
      (TRefined t _ _) -> typeProtectsLabel l t
      TBool l' -> flowCheck l l'
      (TUnion t1 t2) -> do
        typeProtectsLabel' l t1
        typeProtectsLabel' l t2
      (TUnit) -> return () -- Only sound since TUnit is unit 
      TConst s ps -> do
          td <- getTyDef s
          case td of
            TyAbstract -> flowCheck l (mkSpanned $ LConst $ TyLabelVar s)
            TyAbbrev t -> typeProtectsLabel' l t
            StructDef xs -> typeError $ "TODO: typeProtectsLabel for struct"
            EnumDef b -> do
                bdy <- extractEnum ps (show s) b
                flowCheck l advLbl
      (TName n) ->
          flowCheck l (nameLbl n)
      TAdmit -> return ()
      TCase p t1 t2 -> do
       typeProtectsLabel' l t1
       typeProtectsLabel' l t2
      TExistsIdx _ -> do
          b <- flowsTo l advLbl
          if b then return () else typeError $ show $ owlpretty "typeProtectsLabel on exists: label " <> owlpretty l <> owlpretty " does not flow to adv"
      t ->
          error ("Unimp: typeProtectsLabel'" ++ show (owlpretty l <> owlpretty ", " <> owlpretty t))

typeProtectsLabel :: Label -> Ty -> Check ()
typeProtectsLabel l t = laxAssertion $ do
    debug $ owlpretty "Checking if label " <> owlpretty l <> owlpretty " is protected by type " <> owlpretty t
    t' <- normalizeTy t
    typeProtectsLabel' l t'


coveringLabel :: Ty -> Check Label
coveringLabel t = local (set tcScope TcGhost) $ do
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
                ls <- forM xs' $ \(_, t) -> tyLenLbl t
                return $ foldr joinLbl zeroLbl ls
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
    local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxSession)) is1) $
        local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxPId)) is2) $ do                
            debug $ owlpretty "Checking localities of name defs " <> owlpretty nls <> owlpretty " for " <> owlpretty n
            forM_ nls normLocality
            debug $ owlpretty "done"
            checkNameType nt
    local (over (curMod . nameDefs) $ insert n (bind (is1, is2) (BaseDef (nt, nls)))) $ k

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
          local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxSession)) is1) $
              local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxPId)) is2) $ do                
                  normLocality loc
          local (over (curMod . ctrEnv) $ insert n (bind (is1, is2) loc)) $ cont
      DeclSMTOption s1 s2 -> do
        local (over z3Options $ M.insert s1 s2) $ cont
      DeclFun s bnd -> do
          ufs <- view $ curMod . userFuncs
          assert ("Duplicate function: " ++ show s) $ not $ member s ufs
          (((is, ps), xs), a) <- unbind bnd
          local (over inScopeIndices $ mappend $ map (\i -> (i, IdxSession)) is) $ do 
              local (over inScopeIndices $ mappend $ map (\i -> (i, IdxPId)) ps) $ do 
                withVars (map (\x -> (x, (ignore $ show x, Nothing, tData advLbl advLbl))) xs) $ do
                    _ <- inferAExpr a
                    return ()
          local (over (curMod . userFuncs) $ insert s (FunDef bnd)) $ cont
      DeclPredicate s bnd -> do 
        preds <- view $ curMod . predicates
        assert ("Duplicate predicate: " ++ show s) $ not $ member s preds
        ((is, xs), p) <- unbind bnd
        local (over inScopeIndices $ mappend $ map (\i -> (i, IdxGhost)) is) $ do 
                withVars (map (\x -> (x, (ignore $ show x, Nothing, tData advLbl advLbl))) xs) $
                    checkProp p
        local (over (curMod . predicates) $ insert s bnd) $ cont
      DeclName n o -> do
        ensureNoConcreteDefs
        ((is1, is2), ndecl) <- unbind o
        case ndecl of 
          DeclAbstractName -> local (over (curMod . nameDefs) $ insert n (bind (is1, is2) AbstractName)) $ cont
          DeclBaseName nt nls -> addNameDef n (is1, is2) (nt, nls) $ cont
          DeclRO strictness b -> do
              (xs, (a, p, nts, lem)) <- unbind b
              local (over inScopeIndices $ mappend $ map (\i -> (i, IdxSession)) is1) $ do 
                local (over inScopeIndices $ mappend $ map (\i -> (i, IdxPId)) is2) $ do 
                    withVars (map (\x -> (x, (ignore $ show x, Nothing, tData advLbl advLbl))) xs) $ do
                        logTypecheck $ "Checking RO decl: " ++ n
                        _ <- inferAExpr a
                        checkProp p
                        forM_ nts $ \nt -> do
                            checkNameType nt
                            checkROName nt
                        case strictness of
                          ROStrict (Just is) -> do
                              forM_ is $ \i -> do
                                  assert ("Hash index " ++ show i ++ " not in scope") $ i < length nts
                          _ -> return ()
              skipROUnique <- view $ envFlags . fSkipRODisj
              when (not skipROUnique) $ do
                  logTypecheck $ "Checking RO uniqueness of " ++ n
                  checkROUnique n (bind ((is1, is2), xs) (a, p, lem))
                  checkROSelfDisjoint n (bind ((is1, is2), xs) (a, p))
              local (over (curMod . nameDefs) $ insert n $ bind (is1, is2) $ RODef strictness $ bind xs (a, p, nts)) cont
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
          local (over inScopeIndices $ mappend $ map (\i -> (i, IdxSession)) is1) $ do
              local (over inScopeIndices $ mappend $ map (\i -> (i, IdxPId)) is2) $ do
                  normLocality l
          let df = DefHeader isl 
          addDef n df $ cont
      DeclDef n o1 -> do
          ((is1, is2), (l, o2)) <- unbind o1
          (xs, (opreReq, tyAnn, bdy)) <- unbind o2
          let preReq = case opreReq of
                         Nothing -> pTrue
                         Just p -> p
          abs_or_body <- local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxSession)) is1) $ do
              local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxPId)) is2) $ do
                  normLocality l
                  forM_ xs $ \(x, t) -> checkTy $ unembed t
                  withVars (map (\(x, t) -> (x, (ignore $ show x, Nothing, unembed t))) xs) $ do
                      checkProp preReq
                      checkTy tyAnn
                      let happenedProp = pHappened (topLevelPath n) (map mkIVar is1, map mkIVar is2) (map aeVar' $ map fst xs)
                      x <- freshVar
                      case bdy of
                        Nothing -> return $ Nothing
                        Just bdy' -> do
                          onlyCheck <- view $ envFlags . fOnlyCheck
                          let doCheck = (onlyCheck == Nothing) || (onlyCheck == Just n)
                          when doCheck $ do 
                              bdy'' <- ANF.anf bdy'
                              debug $ owlpretty "Checking def body " <> owlpretty n
                              debug $ owlpretty "Doing ANF on: "   <> owlpretty bdy'
                              debug $ owlpretty "Result of anf: "  <> owlpretty bdy''
                              logTypecheck $ "Type checking " ++ n
                              t0 <- liftIO $ getCurrentTime
                              pushLogTypecheckScope
                              local (set tcScope $ TcDef l) $ local (set curDef $ Just n) $ 
                                  withVars [(s2n x, (ignore x, Nothing, mkSpanned $ TRefined tUnit ".req" (bind (s2n ".req") (pAnd preReq happenedProp))))] $ do
                                  _ <- checkExpr (Just tyAnn) bdy''
                                  popLogTypecheckScope
                                  t1 <- liftIO $ getCurrentTime
                                  logTypecheck $ "Finished checking " ++ n ++ " in " ++ show (diffUTCTime t1 t0)
                          return $ Just bdy'
          let is_abs = ignore $ case abs_or_body of
                         Nothing -> True
                         Just _ -> False
          let df = Def $ bind (is1, is2) $ DefSpec is_abs l (bind xs (preReq, tyAnn, abs_or_body))
          addDef n df $ cont
      (DeclCorr ils) -> do
          ensureNoConcreteDefs
          ((is, xs), (l1, l2)) <- unbind ils
          local (over inScopeIndices $ mappend $ map (\i -> (i, IdxGhost)) is) $ do
            withVars (map (\x -> (x, (ignore $ show x, Nothing, tData advLbl advLbl))) xs) $ do
              checkLabel l1
              checkLabel l2
          local (over (curMod . advCorrConstraints) $ \xs -> ils : xs ) $ cont
      (DeclStruct n ixs) -> do
          logTypecheck $ "Checking struct: " ++ n
          (is, xs) <- unbind ixs
          dfs <- view detFuncs
          tvars <- view $ curMod . tyDefs
          assert (show $ owlpretty n <+> owlpretty "already defined") $ not $ member n tvars
          assert (show $ owlpretty n <+> owlpretty "already defined") $ not $ member n dfs
          assert (show $ owlpretty "Duplicate constructor / destructor") $ uniq $ n : map fst xs
          local (set (inScopeIndices) $ map (\i -> (i, IdxGhost)) is) $
              forM_ xs $ \(x, t) -> do
                  checkTy t
                  assert (show $ owlpretty x <+> owlpretty "already defined") $ not $ member x dfs
                  llbl <- tyLenLbl t
                  flowCheck llbl advLbl
          let projs = map (\(x, t) ->  (x, StructProjector n x)) xs 
          local (over (curMod . userFuncs) $ insert n (StructConstructor n)) $ 
              local (over (curMod . userFuncs) $ mappend projs) $ 
                  addTyDef n (StructDef ixs) $ 
                      cont
      (DeclEnum n b) -> do
        (is, bdy) <- unbind b
        local (set (inScopeIndices) $ map (\i -> (i, IdxGhost)) is) $
            mapM_ checkTy $ catMaybes $ map snd bdy
        assert (show $ "Enum " ++ n ++ " must be nonempty") $ length bdy > 0
        let constrs = map (\(x, ot) -> (x, EnumConstructor n x)) bdy 
        let tests = map (\(x, ot) -> (x ++ "?", EnumTest n x)) bdy
        local (over (curMod . userFuncs) $ mappend (constrs ++ tests)) $ 
            addTyDef n (EnumDef b) $
                cont
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

nameExpIsLocal :: NameExp -> Check Bool
nameExpIsLocal ne = 
    case ne^.val of
      NameConst _ (PRes (PDot p s)) _ -> do
          p' <- curModName
          return $ p `aeq` p'
      PRFName ne _ -> nameExpIsLocal ne

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

checkROName :: NameType -> Check ()
checkROName nt =  
    case nt^.val of
      NT_Nonce -> return ()
      NT_StAEAD _ _ _ _ -> return ()
      NT_Enc _ -> return ()
      NT_MAC _ -> return ()
      _ -> typeError $ "Bad RO Name: " ++ show (owlpretty nt)

-- We then fold the list of decls, checking later ones after processing the
-- earlier ones.
checkDecls :: [Decl] -> Check ()
checkDecls [] = return ()
checkDecls (d:ds) = checkDecl d (checkDecls ds)
--
checkDeclsWithCont :: [Decl] -> Check a -> Check a
checkDeclsWithCont [] k = k
checkDeclsWithCont (d:ds) k = checkDecl d $ checkDeclsWithCont ds k

mkForallIdx :: [IdxVar] -> Prop -> Prop
mkForallIdx [] p = p
mkForallIdx (i:is) p = mkSpanned $ PQuantIdx Forall (bind i (mkForallIdx is p))

openROData :: Bind (([IdxVar], [IdxVar]), [DataVar]) (AExpr, Prop) -> (AExpr -> Prop -> Check a) -> Check a
openROData b k = do 
    (((is1, is2), xs), (a, preq)) <- unbind b
    local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxSession)) is1) $
        local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxPId)) is2) $ do                
            withVars (map (\x -> (x, (ignore $ show x, Nothing, tData advLbl advLbl))) xs) $ do
                k a preq 

withTypeErrorHook :: (forall a. String -> Check a) -> Check b -> Check b
withTypeErrorHook f k = do
    local (\e -> e { _typeErrorHook = f }) k 

checkROUnique :: String -> Bind (([IdxVar], [IdxVar]), [DataVar]) (AExpr, Prop, Expr) -> Check ()
checkROUnique roname b = do
    pres <- collectROPreimages
    (((is1, is2), xs), (a, preq, elem)) <- unbind b
    local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxSession)) is1) $
        local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxPId)) is2) $ do                
            withVars (map (\x -> (x, (ignore $ show x, Nothing, tData advLbl advLbl))) xs) $ do
                forM_ pres $ \(pth, p) -> 
                    openROData p $ \a' preq' -> do 
                        elem' <- ANF.anf elem
                        withTypeErrorHook (\x -> typeError' $ "Cannot prove RO disjointness between " ++ roname ++ " and " ++ show (owlpretty pth) ++ ": \n             " ++ x) $ do
                                let pdisj = pImpl (pAnd preq preq') (pNot $ pEq a a')
                                _ <- checkExpr (Just $ tLemma pdisj) elem'
                                return ()

checkROSelfDisjoint :: String -> Bind (([IdxVar], [IdxVar]), [DataVar]) (AExpr, Prop) -> Check ()
checkROSelfDisjoint roname b = do
    (((is1, ps1), xs1), (a1, preq1)) <- unbind b
    (((is2, ps2), xs2), (a2, preq2)) <- unbind b
    when ((length is1 + length ps1 + length xs1) > 0) $ do
        local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxSession)) is1) $
            local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxPId)) ps1) $ do                
                withVars (map (\x -> (x, (ignore $ show x, Nothing, tData advLbl advLbl))) xs1) $ do
                    local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxSession)) is2) $
                        local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxPId)) ps2) $ do                
                            withVars (map (\x -> (x, (ignore $ show x, Nothing, tData advLbl advLbl))) xs2) $ do
                                let idxs_eq = foldr pAnd pTrue $ zipWith (\i1 i2 -> mkSpanned $ PEqIdx (IVar (ignore def) i1) (IVar (ignore def) i2)) (is1 ++ ps1) (is2 ++ ps2)
                                let xs_eq = foldr pAnd pTrue $ zipWith (\x y -> pEq (aeVar' x) (aeVar' y)) xs1 xs2
                                let pdisj = pImpl (pAnd preq1 preq2) $ pImpl (pEq a1 a2) $ (pAnd idxs_eq xs_eq)
                                (_, b) <- SMT.smtTypingQuery $ SMT.symAssert pdisj
                                assert ("RO self disjointness check failed: " ++ roname) b
                                        



checkNameType :: NameType -> Check ()
checkNameType nt = withSpan (nt^.spanOf) $ 
    case nt^.val of
      NT_DH -> return ()
      NT_Sig t -> checkTy t
      NT_Nonce -> return ()
      NT_PRF xs -> do
          assert ("PRF value labels not unique") $ uniq $ map fst xs
          forM_ xs (\(_, (a, t)) -> do
              _ <- inferAExpr a
              checkNameType t)
          (_, b) <- SMT.smtTypingQuery $ SMT.symListUniq (map (fst . snd) xs)
          assert "PRF uniqueness check failed" b
      NT_Enc t -> do
        checkTy t
        debug $ owlpretty "Checking if type " <> owlpretty t <> owlpretty " has public lengths "
        checkTyPubLen t
      NT_StAEAD t xaad p np -> do
          checkTy t
          checkTyPubLen t
          (x, aad) <- unbind xaad
          withVars [(x, (ignore $ show x, Nothing, tData advLbl advLbl))] $ checkProp aad
          checkNoncePattern np
          checkCounter p
      NT_PKE t -> do
          checkTy t
          checkTyPubLen t
      NT_MAC t -> checkTy t

checkNoncePattern :: NoncePattern -> Check ()
checkNoncePattern NPHere = return ()

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
checkParam (ParamIdx i) = local (set tcScope TcGhost) $ checkIdx i
checkParam (ParamName ne) = getNameTypeOpt ne >> return ()

checkTy :: Ty -> Check ()
checkTy t = withSpan (t^.spanOf) $ 
    local (set tcScope $ TcGhost) $
        case t^.val of
          TUnit -> return ()
          TBool l -> checkLabel l
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
                    _ <- extractStruct ps (show s) ib
                    return ()
                EnumDef b -> do
                    _ <- extractEnum ps (show s) b
                    return ()
          (TName n) -> do
              _ <- getNameTypeOpt n
              return ()
          (TExistsIdx it) -> do
              (i, t) <- unbind it
              local (over (inScopeIndices) $ insert i IdxGhost) $ checkTy t
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
              local (set tcScope $ TcGhost) $ checkProp p
              checkTy t1
              checkTy t2
          TAdmit -> return ()





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
                bdy <- extractStruct ps (show s) b
                local (set tcScope $ TcGhost) $ do
                    ls <- forM bdy $ \(_, t) -> tyLenLbl t
                    return $ foldr joinLbl zeroLbl ls
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
                debug $ owlpretty "tyLenLbl for " <> owlpretty t1 <> owlpretty " = " <> owlpretty (joinLbl l1 l2)
                return $ joinLbl l1 l2    
            _ -> tyLenLbl t'
      (TUnion t1 t2) -> do
          l1 <- tyLenLbl t1
          l2 <- tyLenLbl t2
          return $ joinLbl l1 l2
      (TExistsIdx it) -> do
          (i, t) <- unbind it
          l <- local (over (inScopeIndices) $ insert i IdxGhost) $ tyLenLbl t
          return $ mkSpanned $ LRangeIdx $ bind i l
      TAdmit -> return zeroLbl




checkTyPubLen :: Ty -> Check ()
checkTyPubLen t0 = laxAssertion $ do
    l <- tyLenLbl t0
    flowCheck l advLbl

checkLabel :: Label -> Check ()
checkLabel l =
    local (set tcScope TcGhost) $
        case l^.val of
          (LName n) -> do
              _ <- getNameTypeOpt n
              return ()
          LZero -> return ()
          LAdv -> return ()
          LTop -> return ()
          (LJoin l1 l2) -> do
              checkLabel l1
              checkLabel l2
          (LConst (TyLabelVar p))  -> do
              _ <- getTyDef p
              return ()
          (LRangeIdx il) -> do
              (i, l) <- unbind il
              local (over (inScopeIndices) $ insert i IdxGhost) $ checkLabel l

checkProp :: Prop -> Check ()
checkProp p =
    local (set tcScope $ TcGhost) $ withSpan  (p^.spanOf) $ 
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
          (PQuantIdx _ ip) -> do
              (i, p) <- unbind ip
              local (over (inScopeIndices) $ insert i IdxGhost) $ checkProp p
          (PQuantBV _ xp) -> do
              (x, p) <- unbind xp
              withVars [(x, (ignore $ show x, Nothing, tData advLbl advLbl))] $ checkProp p 
          PApp s is xs -> do
              mapM_ checkIdx is
              _ <- mapM inferAExpr xs
              return ()
          PAADOf ne x -> do
              _ <- inferAExpr x
              ni <- getNameInfo ne
              case ni of
                Just (nt, _) -> 
                    case nt^.val of
                      NT_StAEAD _ _ _ _ -> return ()
                      _ -> typeError $ "Wrong name type for " ++ show (owlpretty ne) ++ ": expected StAEAD" 
                Nothing -> typeError $ "Name cannot be abstract here: " ++ show (owlpretty ne)
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
          (PRO x y i) -> do
              _ <- inferAExpr x
              _ <- inferAExpr y
              assert ("weird case for PRO i") $ i >= 0
              return ()
          (PEqIdx i1 i2) -> do
              checkIdx i1
              checkIdx i2



flowsTo :: Label -> Label -> Check Bool
flowsTo l1' l2' = do
    l1 <- normalizeLabel l1'
    l2 <- normalizeLabel l2'
    tyc <- view tyContext
    debug $ owlpretty "Checking " <> owlpretty l1 <+> owlpretty "<=" <+> owlpretty l2
    (fn, b) <- SMT.checkFlows l1 l2
    case b of
      Just r -> do
        debug $ owlpretty "Got " <> owlpretty b <> owlpretty " from " <> owlpretty fn
        return r
      Nothing -> typeError $ show $ owlpretty "Inconclusive: " <> owlpretty l1 <+> owlpretty "<=" <+> owlpretty l2 
      -- <> line <> owlpretty "Under context: " <> owlprettyTyContext tyc  <> owlpretty fn

tryFlowsTo :: Label -> Label -> Check (Maybe Bool)
tryFlowsTo l1' l2' = do
    l1 <- normalizeLabel l1'
    l2 <- normalizeLabel l2'
    tyc <- view tyContext
    debug $ owlpretty "tryFlowsTo: Checking " <> owlpretty l1 <+> owlpretty "<=" <+> owlpretty l2
    (fn, b) <- SMT.checkFlows l1 l2
    return b

decideProp :: Prop -> Check (Maybe Bool)
decideProp p = do
    tyc <- view tyContext
    debug $ owlpretty "Deciding" <+> owlpretty p
    (fn, r) <- SMT.symDecideProp p
    case r of
      Just b -> debug $ owlpretty "Got" <+> owlpretty b <+> owlpretty " from" <> owlpretty fn <+> owlpretty "Under context:" <> owlprettyTyContext tyc
      Nothing -> debug $ owlpretty "Inconclusive" <+> owlpretty " from" <> owlpretty fn <+> owlpretty "Under context:" <> owlprettyTyContext tyc
    return r

flowCheck :: Label -> Label -> Check ()
flowCheck l1 l2 = laxAssertion $ do
    b <- flowsTo l1 l2
    assert (show $ ErrFlowCheck l1 l2) b

-- Ensure l flows to LAdv


stripNameExp :: DataVar -> NameExp -> Check NameExp
stripNameExp x e = 
    case e^.val of
      NameConst _ _ (Just (as, _)) ->
          if x `elem` (concat $ map getAExprDataVars as) then typeError ("stripNameExp: " ++ show (owlpretty x) ++ " is in " ++ show (owlpretty as)) else return e
      _ -> return e

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
          if x `elem` getPropDataVars p' then return pTrue else return p'
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
      PQuantIdx q ip -> do
          (i, p') <- unbind ip
          p'' <- stripProp x p'
          return $ mkSpanned $ PQuantIdx q (bind i p'')
      PQuantBV q xp -> do
          (y, p) <- unbind xp               
          p' <- stripProp x p
          return $ mkSpanned $ PQuantBV q (bind y p')
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
      PRO a1 a2 i -> do
          if x `elem` (getAExprDataVars a1 ++ getAExprDataVars a2) then return pTrue else return p 

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
    assert "Cannot be in ghost here" $ not $ s `aeq` TcGhost        

-- Infer type for expr
checkExpr :: Maybe Ty -> Expr -> Check Ty
checkExpr ot e = withSpan (e^.spanOf) $ do 
    debug $ owlpretty "Inferring expr " <> owlpretty e
    case e^.val of
      ECrypt (CLemma lem) aes -> do -- Type check lemma arguments in ghost
          args <- local (set tcScope TcGhost) $ forM aes $ \a -> do
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
          local (set tcScope $ TcGhost) $ checkProp p
          (fn, b) <- local (set tcScope $ TcGhost) $ SMT.smtTypingQuery $ SMT.symAssert p
          g <- view tyContext
          debug $ owlpretty "Type context for assertion " <> owlpretty p <> owlpretty ":" <> (owlprettyTyContext g)
          assert (show $ ErrAssertionFailed fn p) b
          let lineno =  fst $ begin $ unignore $ e^.spanOf
          getOutTy ot $ tRefined tUnit ("assertion_line_" ++ show lineno) p 
      (EAssume p) -> do
          local (set tcScope $ TcGhost) $ checkProp p
          let lineno =  fst $ begin $ unignore $ e^.spanOf
          getOutTy ot $ tRefined tUnit ("assumption_line_" ++ show lineno) p
      (EAdmit) -> getOutTy ot $ tAdmit
      (EDebug (DebugPrintModules)) -> do
          ms <- view openModules
          liftIO $ putStrLn $ show ms
          getOutTy ot $ tUnit
      (EDebug (DebugResolveANF a)) -> do
          liftIO $ putStrLn $ "Resolving ANF on " ++ show (owlpretty a) ++ ":"
          b <- resolveANF a
          liftIO $ putStrLn $ "Got " ++ show (owlpretty b)
          getOutTy ot $ tUnit
      (EDebug (DebugPrint s)) -> do
          liftIO $ putStrLn s
          getOutTy ot $ tUnit
      (EDebug (DebugPrintTyOf a)) -> do
          t <- local (set tcScope $ TcGhost) $ inferAExpr a
          a' <- resolveANF a
          t' <- normalizeTy t
          liftIO $ putStrLn $ show $ owlpretty "Type for " <> owlpretty a <> owlpretty ": " <> owlpretty t' 
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
                debug $ owlpretty "first case for EUnionCase"
                logTypecheck $ "First case for EUnionCase: " ++ s
                pushLogTypecheckScope
                t1' <- withVars [(x, (ignore s, Nothing, tRefined t1 ".res" (pEq (aeVar ".res") a)))] $ checkExpr ot e
                popLogTypecheckScope
                debug $ owlpretty "first case got" <+> owlpretty t1'
                debug $ owlpretty "second case for EUnionCase"
                logTypecheck $ "Second case for EUnionCase: " ++ s
                pushLogTypecheckScope
                t2' <- withVars [(x, (ignore s, Nothing, tRefined t2 ".res" (pEq (aeVar ".res") a)))] $ checkExpr ot e
                popLogTypecheckScope
                debug $ owlpretty "second case got" <+> owlpretty t2'
                assertSubtype t1' t2'
                getOutTy ot =<< stripTy x t2'
            _ -> do  -- Just continue
                t <- withVars [(x, (ignore s, Nothing, t))] $ checkExpr ot e
                getOutTy ot =<< stripTy x t
      (EBlock k) -> checkExpr ot k
      (ELet e tyAnn anf sx xe') -> do
          case tyAnn of
            Just t -> checkTy t
            Nothing -> return ()
          t1 <- checkExpr tyAnn e
          (x, e') <- unbind xe'
          t2 <- withVars [(x, (ignore sx, anf, t1))] (checkExpr ot e')
          stripTy x t2
      (EChooseIdx ip ik) -> do
          (_, b) <- SMT.symDecideProp $ mkSpanned $ PQuantIdx Exists ip
          (i, k) <- unbind ik
          getOutTy ot =<< case b of
            Just True -> do
                (ix, p) <- unbind ip
                x <- freshVar
                let tx = tLemma (subst ix (mkIVar i) p) 
                to <- local (over inScopeIndices $ insert i IdxGhost) $ do
                    withVars [(s2n x, (ignore x, Nothing, tx))] $ checkExpr ot k
                if i `elem` getTyIdxVars to then
                    return (tExistsIdx (bind i to))
                else return to
            _ -> do
                t' <- local (over (inScopeIndices) $ insert i IdxGhost) $ checkExpr ot k
                if i `elem` getTyIdxVars t' then
                    return (tExistsIdx (bind i t'))
                else return t'
      (EUnpack a ixk) -> do
          t <- inferAExpr a
          ((i, x), e) <- unbind ixk
          getOutTy ot =<< case (stripRefinements t)^.val of
            TExistsIdx jt' -> do
                (j, t') <- unbind jt'
                let tx = tRefined (subst j (mkIVar i) t') ".res" (pEq (aeVar ".res") a) 
                to <- local (over (inScopeIndices) $ insert i IdxGhost) $ do
                    withVars [(x, (ignore $ show x, Nothing, tx))] $ checkExpr ot e
                to' <- stripTy x to
                if i `elem` getTyIdxVars to' then
                    return (tExistsIdx (bind i to'))
                else return to'
            _ -> do
                t' <- local (over (inScopeIndices) $ insert i IdxGhost) $ withVars [(x, (ignore $ show x, Nothing, t))] $ checkExpr ot e
                to' <- stripTy x t'
                if i `elem` getTyIdxVars to' then
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
                (xts, (pr, rt, _)) <- unbind o
                assert (show $ owlpretty "Wrong variable arity for " <> owlpretty f) $ length args == length xts
                argTys <- mapM inferAExpr args
                forM (zip xts argTys) $ \((_, t), t') -> assertSubtype t' (unembed t)
                let (prereq, retTy) = substs (zip (map fst xts) args) (pr, rt)
                (fn, b) <- SMT.smtTypingQuery $ SMT.symAssert prereq
                assert ("Precondition failed: " ++ show (owlpretty prereq) ++ show (owlpretty fn)) b
                let happenedProp = pHappened f (is1, is2) args
                getOutTy ot $ (tRefined retTy ".res" happenedProp)
            _ -> typeError $ "Unreachable"
      (EIf a e1 e2) -> do
          debug $ owlpretty "Checking if at" <+> owlpretty (unignore $ e^.spanOf)
          t <- inferAExpr a
          lt <- coveringLabel t
          flowCheck lt advLbl
          -- debug $ owlpretty "\t" <> owlpretty t <> owlpretty "\t" <> owlpretty (subst (s2n ".res") (aeVar ".pCond") t)
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
      (EFalseElim e) -> do
        (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ mkSpanned PFalse
        if b then getOutTy ot tAdmit else checkExpr ot e
      (ESetOption s1 s2 k) -> do
        local (over z3Options $ M.insert s1 s2) $ checkExpr ot k
      (EForallBV xk) -> do
          (x, k) <- unbind xk
          t <- local (set tcScope TcGhost) $ withVars [(x, (ignore $ show x, Nothing, tData topLbl topLbl))] $ do
              checkExpr Nothing k
          t' <- normalizeTy t
          case t'^.val of
            TRefined (Spanned _ TUnit) _ yp -> do
                (y, p') <- unbind yp
                getOutTy ot $ tLemma $ mkSpanned $ PQuantBV Forall $ bind x $ subst y (aeApp (topLevelPath "unit") [] []) p'
            _ -> typeError $ "Unexpected return type of forall body: " ++ show (owlpretty t')
      (EForallIdx ik) -> do
          (i, k) <- unbind ik
          t <- local (set tcScope TcGhost) $ local (over inScopeIndices $ mappend [(i, IdxGhost)]) $ do
              checkExpr Nothing k
          t' <- normalizeTy t
          case t'^.val of
            TRefined (Spanned _ TUnit) _ yp -> do
                (y, p') <- unbind yp
                getOutTy ot $ tLemma $ mkSpanned $ PQuantIdx Forall $ bind i $ subst y (aeApp (topLevelPath "unit") [] []) p'
            _ -> typeError $ "Unexpected return type of forall body: " ++ show (owlpretty t')
      (EPCase p op k) -> do
          _ <- local (set tcScope TcGhost) $ checkProp p
          doCaseSplit <- case op of
                           Nothing -> return True
                           Just pcond -> do 
                               _ <- local (set tcScope TcGhost) $ checkProp pcond
                               (_, b) <- SMT.smtTypingQuery $ SMT.symAssert pcond
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
                  logTypecheck $ "Case split: " ++ show (owlpretty p)
                  pushLogTypecheckScope
                  (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ mkSpanned PFalse
                  r <- if b then getOutTy ot tAdmit else checkExpr (Just retT) k
                  popLogTypecheckScope
              _ <- withVars [(s2n x, (ignore $ "pcase_false (line " ++ show pcase_line ++ ")", Nothing, tLemma (pNot p)))] $ do
                  logTypecheck $ "Case split: " ++ show (owlpretty $ pNot p)
                  pushLogTypecheckScope
                  (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ mkSpanned PFalse
                  r <- if b then getOutTy ot tAdmit else checkExpr (Just retT) k
                  popLogTypecheckScope
              normalizeTy retT
      (ECase e1 cases) -> do
          debug $ owlpretty "Typing checking case: " <> owlpretty (unignore $ e^.spanOf)
          t <- checkExpr Nothing e1
          debug $ owlpretty "Inferred type " <> owlpretty t <> owlpretty "for argument"
          t <- normalizeTy t
          let t' = stripRefinements t
          (l, otcases) <- case t'^.val of
                            TData l1 l2 _ -> return (l1, Left (tData l1 l2))
                            TOption to -> return (advLbl, Right $ [("Some", Just to), ("None", Nothing)])
                            TConst s ps -> do
                                td <- getTyDef s
                                case td of
                                  EnumDef b -> do
                                      bdy <- extractEnum ps (show s) b
                                      return (advLbl, Right bdy)
                            _ -> typeError $ "Unknown type for case expression: " ++ show (owlpretty t')
          assert (show $ owlpretty "Empty cases on case expression") $ length cases > 0
          flowCheck l advLbl
          branch_tys <- 
              case otcases of
                Left td -> do
                    forM cases $ \(c, ocase) -> 
                        case ocase of
                          Left e -> checkExpr ot e
                          Right (sb, xe) -> do
                              (x, e) <- unbind xe
                              t <- withVars [(x, (sb, Nothing, td))] $ checkExpr ot e
                              case ot of
                                 Just _ -> return t
                                 Nothing -> stripTy x t
                Right tcases -> do
                    forM tcases $ \(c, ot') ->
                        case (ot', lookup c cases) of
                          (_, Nothing) -> typeError $ show $ owlpretty "Case not found: " <> owlpretty c
                          (Nothing, Just (Left e)) -> checkExpr ot e
                          (Just tc, Just (Right (sb, xe))) -> do
                              (x, e) <- unbind xe
                              t <- withVars [(x, (sb, Nothing, tc))] $ checkExpr ot e
                              case ot of
                                Just _ -> return t
                                Nothing -> stripTy x t
                          (_, _) -> typeError $ show $ owlpretty "Mismatch on case: " <> owlpretty c
          case ot of
            Just t -> return t
            Nothing -> do -- Need to synthesize type here. Take the first one
                let t = head branch_tys
                forM_ (tail branch_tys) $ \t' -> assertSubtype t' t
                return t


doAEnc t1 x t args =
  case extractNameFromType t1 of
    Just k -> do
        nt <- local (set tcScope TcGhost) $  getNameType k
        case nt^.val of
          NT_Enc t' -> do
              debug $ owlpretty "Checking encryption for " <> owlpretty k <> owlpretty " and " <> owlpretty t
              b1 <- isSubtype t t'
              if b1 then
                  return $ mkSpanned $ TRefined (tData advLbl advLbl) ".res" $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (aeApp (topLevelPath $ "cipherlen") [] [aeLength x])
              else
                  mkSpanned <$> trivialTypeOf [t1, t]
          _ -> typeError $ show $ ErrWrongNameType k "encryption key" nt
    _ -> do
        debug $ owlpretty "Got extremely wrong case: " <> owlpretty args
        mkSpanned <$> trivialTypeOf [t1, t]

doADec t1 t args = 
    case extractNameFromType t1 of
      Just k -> do
          debug $ owlpretty "Trying nontrivial dec"
          nt <-  local (set tcScope TcGhost) $ getNameType k
          case nt^.val of
            NT_Enc t' -> do
                b2 <- flowsTo (nameLbl k) advLbl
                b <- tyFlowsTo t advLbl -- Public ciphertext
                if ((not b2) && b) then do
                    -- Honest
                    debug $ owlpretty "Honest dec"
                    return $ mkSpanned $ TOption t'
                else if b then do
                    l_corr <- coveringLabelOf [t1, t]
                    return $ mkSpanned $ TOption $ tDataAnn l_corr l_corr "Corrupt adec" -- Change here
                else do
                    debug $ owlpretty "Corrupt dec"
                    l_corr <- coveringLabelOf [t1, t]
                    -- Corrupt
                    return $ tDataAnn l_corr l_corr "Corrupt adec"-- Change here
            _ -> typeError $ show $  ErrWrongNameType k "encryption key" nt
      _ -> do
          l <- coveringLabelOf [t1, t]
          debug $ owlpretty "Trivial dec"
          return $ tData l l -- Change here

owlprettyMaybe :: OwlPretty a => Maybe a -> OwlDoc
owlprettyMaybe x = 
    case x of
      Nothing -> owlpretty "Nothing"
      Just x -> owlpretty "Just" <+> owlpretty x

pNameExpEq :: NameExp -> NameExp -> Prop
pNameExpEq ne1 ne2 = 
    case (ne1^.val, ne2^.val) of
      _ | ne1 `aeq` ne2 -> pTrue
      (NameConst _ p1 _, NameConst _ p2 _) | (not $ p1 `aeq` p2) -> pFalse 
      (NameConst _ _ _, NameConst _ _ _) -> pEq (mkSpanned $ AEGet ne1) (mkSpanned $ AEGet ne2)
      (PRFName x s, PRFName x' s') -> pAnd (pNameExpEq x x') (if s == s' then pTrue else pFalse)
      _ -> pFalse

nameExpNotIn :: NameExp -> [NameExp] -> Prop
nameExpNotIn ne nes = foldr pAnd pTrue $ map (\ne' -> pNot $ pNameExpEq ne ne') nes 

proveDisjointContents :: AExpr -> AExpr -> Check ()
proveDisjointContents x y = do
    ns1 <- getNameContents x
    ns2 <- getNameContents y
    ns1' <- mapM normalizeNameExp ns1
    ns2' <- mapM normalizeNameExp ns2
    let p1 = foldr pAnd pTrue $ map (\ne -> nameExpNotIn ne ns2') ns1' 
    let p2 = foldr pAnd pTrue $ map (\ne -> nameExpNotIn ne ns1') ns2' 
    local (set tcScope TcGhost) $ do
        (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ pOr p1 p2
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

checkROHint :: ROHint -> Check (AExpr, Prop, [NameType])
checkROHint (p, (is, ps), args) = local (set tcScope TcGhost) $ do
    b <- getRO p
    ((ixs, pxs), b') <- unbind b
    (xs, (pre_, req_, nts_)) <- unbind b'
    assert ("Wrong index arity to RO " ++ show (owlpretty p)) $ (length is, length ps) == (length ixs, length pxs)
    assert ("Wrong var arity to RO " ++ show (owlpretty p)) $ length args == length xs
    forM_ is checkIdx
    forM_ ps checkIdx
    _ <- forM args inferAExpr
    return $ substs (zip ixs is) $ substs (zip pxs ps) $ substs (zip xs args) $ (pre_, req_, nts_) 

findGoodROHint :: AExpr -> Int -> [((AExpr, Prop, [NameType]), ROHint)] -> Check NameExp
findGoodROHint a _ [] = typeError $ "Cannot prove " ++ show (owlpretty a) ++ " matches given hints"
findGoodROHint a i (((a', p', _), (pth, inds, args)) : xs) = do
    (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ pAnd p' (pEq a a')
    if b then return (mkSpanned $ NameConst inds pth (Just (args, i))) else findGoodROHint a i xs


checkCryptoOp :: CryptOp -> [(AExpr, Ty)] -> Check Ty
checkCryptoOp cop args = do
    debug $ owlpretty $ "checkCryptoOp:" ++ show (owlpretty cop) ++ " " ++ show (owlpretty args)
    case cop of
      CLemma (LemmaCRH) -> local (set tcScope TcGhost) $ do 
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
      CLemma (LemmaCrossDH n1 n2 n3) -> do
          assert ("Wrong number of arguments to cross_dh_lemma") $ length args == 1
          let [(x, t)] = args
          b <- tyFlowsTo t advLbl
          assert ("Argument to cross_dh_lemma must flow to adv") b
          nt1 <- getNameType n1
          assert ("First argument to cross_dh_lemma must be a DH name") $ (nt1^.val) `aeq` NT_DH
          nt2 <- getNameType n2
          assert ("Second argument to cross_dh_lemma must be a DH name") $ (nt2^.val) `aeq` NT_DH
          nt3 <- getNameType n3
          assert ("Third argument to cross_dh_lemma must be a DH name") $ (nt3^.val) `aeq` NT_DH
          let ns_disj = pAnd (pNot $ pNameExpEq n1 n2) $ pAnd (pNot $ pNameExpEq n1 n3) $ pNot $ pNameExpEq n2 n3
          let dhCombine x y = mkSpanned $ AEApp (topLevelPath "dh_combine") [] [x, y]
          let dhpk x = mkSpanned $ AEApp (topLevelPath "dhpk") [] [x]
          p <- simplifyProp $  pImpl (foldr pAnd pTrue [ns_disj, pNot (pFlow (nameLbl n2) advLbl), pNot (pFlow (nameLbl n3) advLbl)])
                        (pNot $ pEq (dhCombine x (mkSpanned $ AEGet n1))
                                    (dhCombine (dhpk (mkSpanned $ AEGet n2)) (mkSpanned $ AEGet n3)))
   
          return $ tLemma p
      CLemma (LemmaConstant)  -> do
          assert ("Wrong number of arguments to is_constant_lemma") $ length args == 1
          let [(x, _)] = args
          x' <- resolveANF x
          x'' <- normalizeAExpr x'
          let b = isConstant x''
          assert ("Argument is not a constant: " ++ show (owlpretty x'')) b
          return $ tRefined tUnit "._" $ mkSpanned $ PIsConstant x''
      CHash hints i -> do
          assert ("RO hints must be nonempty") $ length hints > 0
          hints_data <- forM hints checkROHint
          let nks = map (map getNameKind) $ map (\(_, _, x)  -> x) hints_data
          let hints_consistent = all (\x -> x == head nks) nks
          assert ("RO hints must have consistent name kinds") $ hints_consistent
          assert ("RO name index out of bounds") $ i < length (head nks)
          ne <- findGoodROHint (mkConcats $ map fst args) i (zip hints_data hints)
          lenConst <- local (set tcScope TcGhost) $ lenConstOfROName $ ne
          solvability <- solvabilityAxioms (mkConcats $ map fst args) ne 
          return $ mkSpanned $ TRefined (tName ne) ".res" $ bind (s2n ".res") $ 
              pAnd (mkSpanned $ PRO (mkConcats $ map fst args) (aeVar ".res") i)
                (pAnd solvability $ pEq (aeLength (aeVar ".res")) lenConst)

      -- 1. Ensure that the hints are nonempty and consistent (name kinds are the same)
      -- 1.5. Check that i is in bounds
      -- 2. One by one, try to find a hint that matches the concats of the args 
      -- 3. If no hint matches, throw an error
      -- 4. If a hint matches, return the corresponding name type, refined with:
      --    - RO solvability axioms
      --    - RO predicate
      CPRF s -> do
          assert ("Wrong number of arguments to prf") $ length args == 2
          let [(_, t1), (a, t)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just k -> do
                nt <-  local (set tcScope TcGhost) $ getNameType k
                case nt^.val of
                  NT_PRF aes -> do
                      case L.find (\p -> fst p == s) aes of
                        Nothing -> typeError $ "Unknown PRF label: " ++ s
                        Just (_, (ae, nt')) -> do
                            (_, b) <- SMT.smtTypingQuery $ SMT.symCheckEqTopLevel [ae] [a]
                            corr <- flowsTo (nameLbl k) advLbl
                            if (not corr) && b then return (mkSpanned $ TName $ prfName k s) else mkSpanned <$> trivialTypeOf [t1, t]
                  _ -> typeError $ "Wrong name type for PRF"
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
                nt <- local (set tcScope TcGhost) $ getNameType k
                case nt^.val of
                  NT_StAEAD tm xaad p' _ -> do
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
                nt <- local (set tcScope TcGhost) $ getNameType k
                case nt^.val of
                  NT_StAEAD tm xaad _ _ -> do
                      b1 <- flowsTo (nameLbl k) advLbl
                      b2 <- tyFlowsTo tnonce advLbl
                      b3 <- tyFlowsTo t advLbl
                      b4 <- tyFlowsTo t2 advLbl
                      if (not b1) && b2 && b3 && b4 then do
                            (x, aad) <- unbind xaad
                            return $ mkSpanned $ TOption $ tRefined tm ".res" $ subst x y aad
                      else if (b2 && b3 && b4) then do 
                          l <- coveringLabelOf [t1, t, t2, tnonce]
                          return $ mkSpanned $ TOption $ tData l l
                      else do
                            -- Corrupt
                            l <- coveringLabel t
                            let l_corr = joinLbl (nameLbl k) l
                            return $ tData l_corr l_corr
                  _ -> mkSpanned <$> trivialTypeOf (map snd args)         
      CPKDec -> do 
          assert ("Wrong number of arguments to pk decryption") $ length args == 2
          let [(_, t1), (_, t)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just k -> do
              nt <- local (set tcScope TcGhost) $  getNameType k
              case nt^.val of
                NT_PKE t' -> do
                    l <- coveringLabel t
                    b1 <- flowsTo l advLbl
                    b2 <- flowsTo (nameLbl k) advLbl
                    if b1 && (not b2) then do
                        -- TODO: is this complete?
                        return $ mkSpanned $ TOption $ mkSpanned $ TUnion t' $ tDataAnn advLbl advLbl "adversarial message"
                    else do
                        let l_corr = joinLbl (nameLbl k) l
                        return $ mkSpanned $ TOption $ tDataAnn l_corr l_corr "corrupt pkdec"
      CPKEnc -> do 
          assert ("Wrong number of arguments to pk encryption") $ length args == 2
          let [(_, t1), (x, t)] = args
          case extractEncPKFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just k -> do
                nt <- local (set tcScope TcGhost) $  getNameType k
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
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just k -> do 
                nt <-  local (set tcScope TcGhost) $ getNameType k
                case nt^.val of
                  NT_MAC t' -> do
                      assertSubtype t t'
                      l <- coveringLabel t'
                      return $ mkSpanned $ TRefined (tData l advLbl) ".res" $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (mkSpanned $ AELenConst "maclen")
                  _ -> mkSpanned <$> trivialTypeOf [t1, t]
      CMacVrfy -> do
          assert ("Wrong number of arguments to mac_vrfy") $ length args == 3
          let [(xt1, t1), (m, mt), (xt, t)] = args
          case extractNameFromType t1 of
            Nothing -> do
                l <- coveringLabelOf [t1, mt, t] 
                return $ tData l l -- Change here
            Just k -> do
                nt <- local (set tcScope TcGhost) $ getNameType k
                case nt^.val of
                  NT_MAC t' -> do
                      l1 <- coveringLabel mt
                      l2 <- coveringLabel t
                      b1 <- flowsTo  l1 advLbl
                      b2 <- flowsTo  l2 advLbl
                      b3 <- flowsTo  (nameLbl k) advLbl
                      if (b1 && b2 && (not b3)) then
                        return $ mkSpanned $ TOption (tRefined t' ".res" $ (pEq (aeVar ".res") m))
                      else
                        let l_corr = joinLbl (nameLbl k) (joinLbl l1 l2) in
                        return $ mkSpanned $ (TData l_corr l_corr (ignore $ Just "corrupt mac")) -- Change here
      CSign -> do
          assert ("Wrong number of arguments to sign") $ length args == 2
          let [(_, t1), (_, t)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just sk -> do
                nt <- local (set tcScope TcGhost) $  getNameType sk
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
                return $ mkSpanned $ TData l l (ignore $ Just $ "corrupt vrfy") 
            Just k -> do 
                nt <-  local (set tcScope TcGhost) $ getNameType k
                case nt^.val of
                  NT_Sig t' -> do
                      l <- coveringLabel t'
                      let l' = joinLbl l advLbl
                      b1 <- tyFlowsTo t2 l'
                      b2 <- tyFlowsTo t3 l'
                      b3 <- flowsTo (nameLbl k) advLbl
                      if (b1 && b2 && (not b3)) then return (mkSpanned $ TOption t')
                                                else do
                                                 l_corr <- coveringLabelOf [t1, t2, t3]
                                                 return $ mkSpanned $ (TData l_corr l_corr $ ignore $ Just "corrupt vrfy") -- Change here
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
          (args, (pr1, t1, _)) <- unbind pty
          (args', (pr2, t2, _)) <- unbind pty'
          assert ("Def locality mismatch") $ (bind is1 l1) `aeq` (bind is' l1')
          assert ("Def prereq mismatch") $ (bind is1 $ bind args pr1) `aeq` (bind is' $ bind args' pr2)
          assert ("Def return ty mismatch") $ (bind is1 $ bind args t1) `aeq` (bind is' $ bind args' t2)
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
      _ -> typeError $ "Unhandled name def matches case"


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
          debug $ owlpretty "Checking moduleMatches of arguments"
          moduleMatches t2 t1
          debug $ owlpretty "Checking moduleMatches of body"
          (x, md1) <- unbind xmd1
          (y, md2_) <- unbind ymd2
          let md2 = subst y (PPathVar (ClosedPathVar $ ignore $ show x) x) md2_
          p <- curModName
          local (over modContext $ insert x t1) $ 
                moduleMatches md1 md2
      (MBody xmd1, MBody ymd2) -> do
          (x, md1) <- unbind xmd1
          (y, md2_) <- unbind ymd2
          debug $ owlpretty "moduleMatches with " <> owlpretty x <> owlpretty " and " <> owlpretty y
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
    (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ mkSpanned PFalse
    let info = if b then [E.Note "Inconsistent type context detected. Try using false_elim?"] else []
    tyc <- removeAnfVars <$> view tyContext 
    let rep = E.Err Nothing msg [(pos, E.This msg)] info
    let diag = E.addFile (E.addReport def rep) (fn) f  
    e <- ask
    E.printDiagnostic S.stdout True True 4 E.defaultStyle diag 
    liftIO $ putDoc $ owlpretty "Type context" <> line <> pretty "===================" <> line <> owlprettyTyContext tyc <> line
    writeSMTCache
    Check $ lift $ throwError e
