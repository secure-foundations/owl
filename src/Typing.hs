{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module Typing where
import AST
import qualified Data.Map.Strict as M
import Error.Diagnose.Position
import Data.Default (Default, def)
import qualified Data.Map.Ordered as OM
import qualified Data.Set as S
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
import Control.Lens
import LabelChecking
import TypingBase
import qualified SMT as SMT
import qualified SMTBase as SMT
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe
import qualified Text.Parsec as P
import Parse

emptyModBody :: IsModuleType -> ModBody
emptyModBody t = ModBody t mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty

-- extend with new parts of Env -- ok
emptyEnv :: Flags -> IO Env
emptyEnv f = do
    r <- newIORef 0
    return $ Env f initDetFuncs mempty TcGhost mempty mempty mempty [(Nothing, emptyModBody ModConcrete)] mempty interpUserFunc r


assertEmptyParams :: [FuncParam] -> String -> Check ()
assertEmptyParams ps f =
    assert (ignore def) ("Function " ++ f ++ " does not expect params") $ length ps == 0

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
    return $ TData l l

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
mkRefined t p = TRefined t (bind (s2n ".res") $ p $ aeVar ".res")

initDetFuncs :: Map String (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX)
initDetFuncs = withNormalizedTys $ [
    mkSimpleFunc "UNIT" 0 $ \args -> do
        return $ TUnit,
    mkSimpleFunc "TRUE" 0 $ \args -> do
        return $ TBool zeroLbl,
    mkSimpleFunc "FALSE" 0 $ \args -> do
        return $ TBool zeroLbl,
    ("eq", (2, \ps args -> do 
        assert (ignore def) ("Bad params") $ length ps == 0
        case args of
          [(a1, t1), (a2, t2)] -> do
              l1 <- coveringLabel t1
              l2 <- coveringLabel t2
              let true = aeApp (topLevelPath $ "TRUE") [] []
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
              if b then return (TOption t) else return (TData l l) 
          _ -> typeError (ignore def) $ show $ ErrBadArgs "Some" (map snd args))),
    ("None", (0, \ps args -> do
        case (ps, args) of
          ([ParamTy t], []) -> do
              return (TOption t)
          _ -> typeError (ignore def) $ show $ ErrBadArgs "None" (map snd args))),
    ("andb", (2, \ps args -> do
        assert (ignore def) ("Bad params") $ length ps == 0
        case args of
          [(x, t1), (y, t2)] -> do
            l1 <- coveringLabel t1
            l2 <- coveringLabel t2
            let l = joinLbl l1 l2
            let tr = aeApp (topLevelPath $ "TRUE") [] []
            assertSubtype t1 (mkSpanned $ TBool l)
            assertSubtype t2 (mkSpanned $ TBool l)
            return $ TRefined (mkSpanned $ TBool l) (bind (s2n ".res") $ pImpl (pEq (aeVar ".res") tr) (pAnd (pEq x tr) (pEq y tr)))
          _ -> typeError (ignore def) "Bad args for andb")),
    mkSimpleFunc "length" 1 $ \args -> do
        case args of
          [t] -> do
              l <- tyLenLbl t
              return $ TData l l
          _ -> typeError (ignore def) $ show $ ErrBadArgs "length" args,
    mkSimpleFunc "plus" 2 $ \args -> trivialTypeOf args,
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
                    return $ TRefined (mkSpanned $ TVK n) $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (mkSpanned $ AELenConst "vk")
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
                _ -> typeError (x^.spanOf) $ "Wrong name types for dh_combine"
          _ -> typeError (ignore def) $ "Bad params to dh_combine: expected two name params"
                   )),
    ("checknonce", (2, \ps args ->
        case (ps, args) of
          ([], [(x, t1), (y, t2)]) ->
              case ((stripRefinements t1)^.val, (stripRefinements t2)^.val) of
                (TName n, TName m) -> do
                  debug $ pretty "Checking name " <> pretty n <> pretty " against " <> pretty m
                  if n `aeq` m then return $ TRefined (mkSpanned $ TBool zeroLbl) (bind (s2n ".res") (pEq (aeVar ".res") (aeApp (topLevelPath $ "TRUE") [] [])))
                  else case (n^.val, m^.val) of
                       (BaseName (is1, is1') a, BaseName (is2, is2') b) | a `aeq` b -> do
                           let p =  foldr pAnd pTrue $ map (\(i, j) -> mkSpanned $ PEqIdx i j) $ zip (is1 ++ is1') (is2  ++ is2')
                           return $ TRefined (mkSpanned $ TBool advLbl) (bind (s2n ".res") (pImpl (pEq (aeVar ".res") (aeApp (topLevelPath $ "TRUE") [] [])) p))
                       _ -> do
                           l <- coveringLabelOf $ map snd args
                           return $ TBool l
                (TName n, m) -> do
                  nt <-  local (set tcScope TcGhost) $ getNameType n
                  case nt^.val of
                    NT_Nonce -> do
                        l <- coveringLabel (mkSpanned m)
                        return $ TRefined (mkSpanned $ TBool l) (bind (s2n ".res") (pImpl (pEq (aeVar ".res") (aeApp (topLevelPath $ "TRUE") [] [])) (pAnd (pFlow (nameLbl n) l) (pEq x y))))
                    _ -> trivialTypeOf $ map snd args
                (m, TName n) -> do
                  nt <-  local (set tcScope TcGhost) $ getNameType n
                  case nt^.val of
                    NT_Nonce -> do
                        l <- coveringLabel (mkSpanned m)
                        return $ TRefined (mkSpanned $ TBool l) (bind (s2n ".res") (pImpl (pEq (aeVar ".res") (aeApp (topLevelPath $ "TRUE") [] [])) (pAnd (pFlow (nameLbl n) l) (pEq x y))))
                    _ -> trivialTypeOf $ map snd args
                _ -> do
                  l <- coveringLabelOf $ map snd args
                  return $ TBool l
          _ -> typeError (ignore def) $ "Wrong parameters to checknonce"
    ))
    ]

interpUserFunc :: Ignore Position -> ResolvedPath -> ModBody -> UserFunc -> Check (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX)
interpUserFunc pos pth md (StructConstructor tv) = do
    case lookup tv (md^.tyDefs) of
      Just (StructDef idf) -> do
          let (is_ar, ar) = let (xs, ys) = unsafeUnbind idf in (length xs, length ys)
          return (ar, \ps xs -> do
              forM_ ps checkParam
              nts <- extractStruct pos ps (show tv) idf 
              assert pos (show $ pretty "Index arity mismatch on struct constructor") $ length ps == is_ar 
              if length xs == ar then do
                b <- foldM (\acc i -> do
                    b1 <- isSubtype (snd $ xs !! i) (snd $ nts !! i) 
                    return $ acc && b1) True [0..(length xs - 1)]
                if b then return (TRefined (mkSpanned $ TConst (PRes $ PDot pth tv) ps) (bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (sumOfLengths (map fst xs)))) else trivialTypeOf (map snd xs)
              else trivialTypeOf (map snd xs))
      _ -> typeError pos $ "Unknown struct: " ++ show tv
interpUserFunc pos pth md (StructProjector tv field) = do
    case lookup tv (md^.tyDefs) of
      Just (StructDef idf) -> do
          let (is_ar, ar) = let (xs, ys) = unsafeUnbind idf in (length xs, length ys)
          return (1, \ps args -> do
              forM_ ps checkParam
              nts <- extractStruct pos ps (show tv) idf 
              assert pos (show $ pretty "Index arity mismatch on struct constructor") $ length ps == is_ar 
              case lookup field nts of
                Just t -> do
                  b <- isSubtype (snd $ args !! 0) (mkSpanned $ TConst (PRes $ PDot pth tv) ps)
                  if b then return (t^.val) else trivialTypeOf $ map snd args
                Nothing -> typeError pos $ "Unknown struct field: " ++ field)
      _ -> typeError pos $ "Unknown struct: " ++ show tv
interpUserFunc pos pth md (EnumConstructor tv variant) = do
    case lookup tv (md^.tyDefs) of
      Just (EnumDef idf) -> do
          let (is_ar, enum_map) = let (xs, ys) = unsafeUnbind idf in (length xs, ys)
          ar <- case lookup variant enum_map of
                  Nothing -> typeError pos $ "Unknown enum variant: " ++ variant
                  Just Nothing -> return 0
                  Just (Just _) -> return 1
          return (ar, \ps args -> do 
              forM_ ps checkParam
              nts <- extractEnum pos ps (show tv) idf
              assert pos (show $ pretty "Index arity mismatch on enum constructor") $ length ps == is_ar 
              let ot = fromJust $ lookup variant nts
              case ot of
                Nothing -> return $ TRefined (mkSpanned $ TConst (PRes $ PDot pth tv) (ps)) (bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (aeLenConst "tag"))
                Just t -> do
                    b <- isSubtype (snd $ args !! 0) t
                    if b then return (TRefined (mkSpanned $ TConst (PRes $ PDot pth tv) (ps))
                                                          (bind (s2n ".res") $
                                                              pEq (aeLength (aeVar ".res"))
                                                                  (aeApp (topLevelPath $ "plus") [] [aeLength (fst $ args !! 0), aeLenConst "tag" ])))
                    else trivialTypeOf (map snd args))
      _ -> typeError pos $ "Unknown enum: " ++ show tv 
interpUserFunc pos pth md (EnumTest tv variant) = do
    return $ snd $ mkSimpleFunc (variant ++ "?") 1 $ \args ->
        case args of
          [t] -> 
              case (stripRefinements t)^.val of
                TConst s _ | s `aeq` (PRes $ PDot pth tv) -> return $ TBool advLbl
                _ -> do
                    l <- coveringLabel t
                    return $ TBool l
interpUserFunc pos pth md (UninterpUserFunc f ar) = do
    return $ (ar, withNoParams (show f) $ \args -> do
        l <- coveringLabelOf $ map snd args
        return $ TRefined (tData l l) $ bind (s2n ".res") (pEq (aeVar ".res") (aeApp (PRes $ PDot pth f) [] (map fst args))))



-- Normalize a type expression. Only nontrivial computations are to normalize a
-- nested refinement, and to normalize a case whether a name n is honest.
normalizeTy :: Ty -> Check Ty
normalizeTy t0 =
    case t0^.val of
    TUnit -> return tUnit
    (TCase p t1 t2) -> do
        ob <- decideProp p
        t1' <- normalizeTy t1
        t2' <- normalizeTy t2
        case ob of
          Nothing -> do
              b1 <- isSubtype t1 t2
              b2 <- isSubtype t2 t1
              if (b1 && b2) then return t1 else return $ Spanned (t0^.spanOf) $ TCase p t1' t2'
          Just b -> return $ if b then t1' else t2'
    (TOption t) -> do
        t' <- normalizeTy t
        return $ Spanned (t0^.spanOf) $ TOption t'
    (TRefined (Spanned _ (TRefined t xp1)) yp2) -> do  -- x:(y:t{p1}){p2} --> x:t{p1 /\ p2}
        (x, p1) <- unbind xp1
        (y, p2) <- unbind yp2
        normalizeTy $ Spanned (t0^.spanOf) $ TRefined t $ bind (s2n "_x") $ pAnd (subst x (aeVar "_x") p1) (subst y (aeVar "_x") p2)
    (TRefined t p) -> do
        t' <- normalizeTy t
        return $ Spanned (t0^.spanOf) $ TRefined t' p
    (TUnion t1 t2) -> do
        t1' <- normalizeTy t1
        t2' <- normalizeTy t2
        return $ Spanned (t0^.spanOf) $ TUnion t1' t2'
    (TData l1 l2) -> do
        l1' <- normalizeLabel l1
        l2' <- normalizeLabel l2
        return $ Spanned (t0^.spanOf) $ TData l1' l2'
    (TDataWithLength l a) -> do
        l' <- normalizeLabel l
        return $ Spanned (t0^.spanOf) $ TDataWithLength l' a
    (TBool l) -> do
        l' <- normalizeLabel l
        return $ Spanned (t0^.spanOf) $ TBool l'
    (TName n) -> return t0
    (TVK n) -> return t0
    (TDH_PK n) -> return t0
    (TEnc_PK n) -> return t0
    (TSS n m) -> return t0
    TConst s ps -> do
        td <- getTyDef (t0^.spanOf) s
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
        t' <- local (over (inScopeIndices) $ insert x IdxGhost) $ normalizeTy t
        return $ Spanned (t0^.spanOf) $ TExistsIdx $ bind x t'
    TAdmit -> return t0

normalizeLabel :: Label -> Check Label
normalizeLabel l = do                
    debug $ pretty "Normalizing " <> pretty l
    normLabel l


-- Subtype checking, assuming the types are normalized

isSubtype' t1 t2 =
    case (t1^.val, t2^.val) of
      _ | isSingleton t2 -> do 
          debug $ pretty "Trying singleton query: " <> pretty t2
          (_, b) <- SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2
          debug $ pretty "Singleton query: " <> pretty t1 <> pretty "<=" <> pretty t2 <> pretty ": " <> pretty b
          return b 
      (TCase p t1' t2', _) -> do
          debug $ pretty "Checking subtype for TCase: " <> pretty t1 <> pretty " <= " <> pretty t2
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
      (TRefined t1' p1, TRefined t2' p2) -> do
        b1 <- isSubtype' t1' t2'
        (_, b) <- SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2
        return $ b1 && b
      (TUnit, TRefined (Spanned _ TUnit) p) -> do
        x' <- freshVar
        isSubtype' (tRefined tUnit (bind (s2n "_x") pTrue)) t2
      (TRefined t _, t') | (t^.val) `aeq` t' -> return True
      (_, TRefined t p) -> do
          b1 <- isSubtype' t1 t
          (_, b2) <- SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2
          return $ b1 && b2
      (_, TUnit) -> snd <$> (SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2)
      (TUnit,  _) -> do
        isSubtype' (tRefined (tData zeroLbl zeroLbl) $ bind (s2n "_x") (pEq (aeVar "_x") (aeApp (topLevelPath $ "UNIT") [] []))) t2
      (TBool l1, TBool l2) -> flowsTo (t1^.spanOf) l1 l2
      (TConst x ps1, TConst y ps2) | (x `aeq` y) -> do
          td <- getTyDef (t1^.spanOf) x
          case td of
            EnumDef _ -> do
                case (ps1, ps2) of
                  (ParamLbl l1 : ps1', ParamLbl l2 : ps2') | ps1' `aeq` ps2' -> flowsTo (t1^.spanOf) l1 l2
                  _ -> return False
            StructDef _ -> do
                assert (t1^.spanOf) (show $ pretty "Func param arity mismatch on struct") $ length ps1 == length ps2
                qs <- forM (zip ps1 ps2) $ \(p1, p2) ->
                    case (p1, p2) of
                      (ParamIdx i1, ParamIdx i2) -> return $ mkSpanned $ PEqIdx i1 i2
                      _ -> typeError (t1^.spanOf) $ "Bad param to struct: didn't get index"
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
      (TName n, TName m) ->
          case (n^.val, m^.val) of
            (BaseName (is1, is1') a, BaseName (is2, is2') b) | a `aeq` b -> do
              debug $ pretty "Equality query on indices " <> pretty (is1 ++ is1') <> pretty " and " <> pretty (is2 ++ is2')
              let p =  foldr pAnd pTrue $ map (\(i, j) -> mkSpanned $ PEqIdx i j) $ zip (is1 ++ is1') (is2 ++ is2')
              (_, b) <- SMT.smtTypingQuery $ SMT.symAssert p
              return b
            _ -> return False
      (t, TDataWithLength l a) -> do
          debug $ pretty "Checking TDataWithLength with " <> pretty t1 <> pretty " <= " <> pretty t2
          b1 <- isSubtype' t1 (tData l l)
          (_, b) <- SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2
          return $ b1 && b
      (t, TData l1 l2) -> do
        l2' <- tyLenLbl t1
        b1 <- tyFlowsTo t1 l1 
        b2 <- flowsTo (t1^.spanOf) l2' l2
        return $ b1 && b2
      (TRefined t _, _) -> isSubtype' t t2
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
          b1 <- flowsTo (t^.spanOf) (joinLbl (nameLbl n) advLbl) l
          b2 <- flowsTo (t^.spanOf) (joinLbl (nameLbl m) advLbl) l
          return $ b1 || b2
      _ -> do
          l1 <- coveringLabel t
          flowsTo (t^.spanOf) l1 l

-- We check t1 <: t2  by first normalizing both
isSubtype :: Ty -> Ty -> Check Bool
isSubtype t1 t2 = do
    debug $ pretty (unignore $ t1^.spanOf) <> pretty (unignore $ t2^.spanOf) <> pretty "Checking subtype of " <> pretty t1 <> pretty " and " <> pretty t2
    t1' <- normalizeTy t1
    t2' <- normalizeTy t2
    b <- isSubtype' t1' t2'
    debug $ pretty "Subtype of " <> pretty t1 <> pretty " and " <> pretty t2 <> pretty ": " <> pretty b
    return b



assertSubtype :: Ty -> Ty -> Check ()
assertSubtype t1 t2 = laxAssertion $ do
    tyc <- view tyContext
    debug $ pretty "Asserting subtype " <> pretty t1 <> pretty " <= " <> pretty t2 <> pretty "Under context: " <> prettyTyContext tyc
    t1' <- normalizeTy t1
    t2' <- normalizeTy t2
    b <- isSubtype' t1' t2'
    assert (t1^.spanOf) (show $ ErrCannotProveSubtype t1' t2') b

typeProtectsLabel' :: Label -> Ty -> Check ()
typeProtectsLabel' l t0 =
    laxAssertion $ case t0^.val of
      (TData l' _) -> flowCheck (t0^.spanOf) l l'
      (TDataWithLength l' _) -> flowCheck (t0^.spanOf) l l'
      (TOption t) -> flowCheck (t0^.spanOf) l advLbl
      (TRefined t _) -> typeProtectsLabel l t
      TBool l' -> flowCheck (t0^.spanOf) l l'
      (TUnion t1 t2) -> do
        typeProtectsLabel' l t1
        typeProtectsLabel' l t2
      (TUnit) -> return () -- Only sound since TUnit is unit 
      TConst s ps -> do
          td <- getTyDef (t0^.spanOf) s
          case td of
            TyAbstract -> flowCheck (t0^.spanOf) l (mkSpanned $ LConst $ TyLabelVar s)
            TyAbbrev t -> typeProtectsLabel' l t
            StructDef xs -> typeError (t0^.spanOf) $ "TODO: typeProtectsLabel for struct"
            EnumDef b -> do
                bdy <- extractEnum (t0^.spanOf) ps (show s) b
                flowCheck (t0^.spanOf) l advLbl
      (TName n) ->
          flowCheck (t0^.spanOf) l (nameLbl n)
      TAdmit -> return ()
      TCase p t1 t2 -> do
       typeProtectsLabel' l t1
       typeProtectsLabel' l t2
      TExistsIdx _ -> do
          b <- flowsTo (t0^.spanOf) l advLbl
          if b then return () else typeError (t0^.spanOf) $ show $ pretty "typeProtectsLabel on exists: label " <> pretty l <> pretty " does not flow to adv"
      t ->
          error ("Unimp: typeProtectsLabel'" ++ show (pretty l <> pretty ", " <> pretty t))

typeProtectsLabel :: Label -> Ty -> Check ()
typeProtectsLabel l t = laxAssertion $ do
    debug $ pretty "Checking if label " <> pretty l <> pretty " is protected by type " <> pretty t
    t' <- normalizeTy t
    typeProtectsLabel' l t'


coveringLabel :: Ty -> Check Label
coveringLabel t = do
    t' <- normalizeTy t
    coveringLabel' t'


addDef :: Ignore Position -> String -> Def -> Check a -> Check a
addDef pos n df cont = do
    dfs <- view $ curMod . defs
    case (df, lookup n dfs) of
      (_, Nothing) -> local (over (curMod . defs) $ insert n df) $ cont
      (DefHeader _, Just _) -> typeError pos $ "Def already defined: " ++ n
      (Def isdp, Just (DefHeader bl)) -> do
          (is, DefSpec _ l _) <- unbind isdp
          assert pos ("Locality mismatch for " ++ n) $ (bind is l) `aeq` bl 
          local (over (curMod . defs) $ insert n df) $ cont
      (Def isdp, Just (Def isdp')) -> do
          (is, DefSpec abs1 l1 ret1) <- unbind isdp
          (_, DefSpec abs2 _ _) <- unbind isdp'
          assert pos ("Duplicate abstract def: " ++ n) $ not (unignore abs1) 
          assert pos ("Def already defined: " ++ n) $ unignore abs2
          defMatches pos n (Just $ Def isdp) (Def isdp') 
          local (over (curMod . defs) $ insert n df) $ cont


addTyDef :: TyVar -> TyDef -> Check a -> Check a
addTyDef s td k = do
    tds <- view $ curMod . tyDefs
    case lookup s tds of
      Nothing -> local (over (curMod . tyDefs) $ insert s td) k 
      Just TyAbstract -> do
          -- Check if length label of td flows to adv
          len_lbl <- case td of
            EnumDef bts -> typeError (ignore def) $ show $ pretty "Cannot assign abstract type " <> pretty s <> pretty " to enum def "
            StructDef sd -> do
                (is, xs') <- unbind sd
                assert (ignore def) (show $ pretty "Cannot assign abstract type " <> pretty s <> pretty " to indexed struct") $ length is == 0
                ls <- forM xs' $ \(_, t) -> tyLenLbl t
                return $ foldr joinLbl zeroLbl ls
            TyAbbrev t -> tyLenLbl t
            TyAbstract -> typeError (ignore def) $ show $ pretty "Overlapping abstract types: " <> pretty s
          len_lbl' <- tyLenLbl $ mkSpanned $ TConst (topLevelPath s) []
          local (over (curMod . flowAxioms) $ \xs -> (len_lbl, len_lbl') : (len_lbl', len_lbl) : xs ) $
              local (over (curMod . tyDefs) $ insert s td) $
                  k
      Just _ -> typeError (ignore def) $ show $ pretty "Type already defined: " <> pretty s

addNameDef :: String -> ([IdxVar], [IdxVar]) -> (NameType, [Locality]) -> Check a -> Check a
addNameDef n (is1, is2) (nt, nls) k = do
    md <- view curMod
    _ <- case lookup n (md ^. nameEnv) of
      Nothing -> return ()
      Just o -> do
        ((is1', is2'), ntnlsOpt') <- unbind o
        case ntnlsOpt' of
          Nothing -> assert (nt^.spanOf) (show $ pretty "Indices on abstract and concrete def of name" <+> pretty n <+> pretty "do not match") $
                        (length is1 == length is1' && length is2 == length is2')
          Just _ -> typeError (ignore def) $ "Duplicate name: " ++ n
    assert (nt^.spanOf) (show $ pretty "Duplicate indices in definition: " <> pretty (is1 ++ is2)) $ UL.allUnique (is1 ++ is2)
    local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxSession)) is1) $
        local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxPId)) is2) $ do                
            debug $ pretty "Checking localities of name defs " <> pretty nls <> pretty " for " <> pretty n
            forM_ nls (normLocality (nt^.spanOf))
            debug $ pretty "done"
            checkNameType nt
    local (over (curMod . nameEnv) $ insert n (bind (is1, is2) (Just (nt, nls)))) $ k

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
          assert (me^.spanOf) (show $ pretty "Not a module type: " <> pretty (unembed t)) $ kind_t1 == ModType
          t1Concrete <- makeModDefConcrete t1
          r <- local (over modContext $ insert x t1Concrete) $ 
                  inferModuleExp k
          return $ MFun s t1 (bind x r)
      ModuleApp e1 arg@(PRes argp) -> do
          md <- inferModuleExp e1 
          case md of
            MBody _ -> typeError (me^.spanOf) $ "Not a functor: " ++ show e1
            MFun _ s xd -> do
              argd <- getModDef (me^.spanOf) argp
              kind_argd <- modDefKind argd
              assert (me^.spanOf) ("Not a module: " ++ show argp) $ kind_argd == ModConcrete
              moduleMatches (me^.spanOf) argd s 
              (x, d) <- unbind xd
              return $ subst x argp d
      ModuleVar pth@(PRes (PDot p s)) -> do
          md1 <- openModule (me^.spanOf) p
          case lookup s (md1^.modules) of 
            Just b -> return b
            Nothing -> typeError (me^.spanOf) $ "Unknown module or functor: " ++ show pth
      ModuleVar pth@(PRes (PPathVar OpenPathVar x)) -> do
          cm <- view openModules
          case lookup (Just x) cm of
              Just md -> return $ MBody $ bind x md
              Nothing -> typeError (me^.spanOf) $ "Unknown module or functor: " ++ show pth
      ModuleVar pth@(PRes (PPathVar (ClosedPathVar _) x)) -> do
          mc <- view modContext
          case lookup x mc of
            Just b -> return b
            Nothing ->  typeError (me^.spanOf) $ "Unknown module or functor: " ++ show pth
      _ -> error $ "Unknown case: " ++ show me

singleLineSpan :: Ignore Position -> Ignore Position
singleLineSpan i = 
    ignore $ go $ unignore i
        where
            go (Position b e i) = Position b (f b) i
            f b = (fst b, 100)

                  
checkDecl :: Decl -> Check a -> Check a
checkDecl d cont = 
    case d^.val of
      (DeclLocality n dcl) -> 
          case dcl of
            Left i -> local (over (curMod . localities) $ insert n (Left i)) $ cont
            Right (PRes pth@(PDot p s)) -> do
                md <- openModule (d^.spanOf) p
                case lookup s (md^.localities) of 
                  Nothing -> typeError (d^.spanOf) $ "Unknown locality: " ++ show pth
                  Just _ -> local (over (curMod . localities) $ insert n (Right pth)) $ cont
      DeclInclude _ -> error "Include found during type inference"
      DeclCounter n isloc -> do
          ((is1, is2), loc) <- unbind isloc
          local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxSession)) is1) $
              local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxPId)) is2) $ do                
                  normLocality (d^.spanOf) loc
          local (over (curMod . ctrEnv) $ insert n (bind (is1, is2) loc)) $ cont
      DeclName n o -> do
        ((is1, is2), ntnlsOpt) <- unbind o
        case ntnlsOpt of
          Nothing ->  local (over (curMod . nameEnv) $ insert n (bind (is1, is2) Nothing)) $ cont
          Just (nt, nls) -> addNameDef n (is1, is2) (nt, nls) $ cont
      DeclModule n imt me omt -> do
          md <- case me^.val of
                  ModuleVar (PRes p) -> return $ MAlias p 
                  _ -> inferModuleExp me
          kind_md <- modDefKind md
          case imt of
            ModConcrete -> assert (d^.spanOf) ("Expected module, got module type: " ++ show (pretty me)) $ kind_md == imt
            ModType -> assert (d^.spanOf) ("Expected module type, got module: " ++ show (pretty me)) $ kind_md == imt
          case omt of
            Nothing -> return ()
            Just mt -> do
              mdt <- inferModuleExp mt
              kind_mdt <- modDefKind mdt
              assert (d^.spanOf) ("Expected module type: " ++ show (pretty mt)) $ kind_mdt == ModType
              moduleMatches (singleLineSpan $ d^.spanOf) md mdt
          local (over (curMod . modules) $ insert n md) $ cont
      DeclDefHeader n isl -> do
          ((is1, is2), l) <- unbind isl
          local (over inScopeIndices $ mappend $ map (\i -> (i, IdxSession)) is1) $ do
              local (over inScopeIndices $ mappend $ map (\i -> (i, IdxPId)) is2) $ do
                  normLocality (d^.spanOf) l
          let df = DefHeader isl 
          addDef (d^.spanOf) n df $ cont
      DeclDef n o1 -> do
          ((is1, is2), (l, o2)) <- unbind o1
          (xs, (opreReq, tyAnn, bdy)) <- unbind o2
          let preReq = case opreReq of
                         Nothing -> pTrue
                         Just p -> p
          abs_or_body <- local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxSession)) is1) $ do
              local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxPId)) is2) $ do
                  normLocality (d^.spanOf) l
                  forM_ xs $ \(x, t) -> checkTy $ unembed t
                  withVars (map (\(x, t) -> (x, (ignore $ show x, unembed t))) xs) $ do
                      checkProp preReq
                      checkTy tyAnn
                      let happenedProp = pHappened (topLevelPath n) (map mkIVar is1, map mkIVar is2) (map aeVar' $ map fst xs)
                      x <- freshVar
                      case bdy of
                        Nothing -> return $ Nothing
                        Just bdy' -> do
                          bdy'' <- ANF.anf bdy'
                          debug $ pretty "Checking def body " <> pretty n
                          debug $ pretty "Result of anf: "  <> pretty bdy''
                          local (set tcScope $ TcDef l) $
                              withVars [(s2n x, (ignore x, mkSpanned $ TRefined tUnit (bind (s2n ".req") (pAnd preReq happenedProp))))] $ do
                              t <- checkExpr (Just tyAnn) bdy''
                              return $ Just bdy'
          let is_abs = ignore $ case abs_or_body of
                         Nothing -> True
                         Just _ -> False
          let df = Def $ bind (is1, is2) $ DefSpec is_abs l (bind xs (preReq, tyAnn, abs_or_body))
          addDef (d^.spanOf) n df $ cont
      (DeclCorr l1 l2) -> do
          checkLabel l1
          checkLabel l2
          local (over (curMod . advCorrConstraints) $ \xs -> (l1, l2) : xs ) $ cont
      (DeclStruct n ixs) -> do
          (is, xs) <- unbind ixs
          dfs <- view detFuncs
          tvars <- view $ curMod . tyDefs
          assert (d^.spanOf) (show $ pretty n <+> pretty "already defined") $ not $ member n tvars
          assert (d^.spanOf) (show $ pretty n <+> pretty "already defined") $ not $ member n dfs
          assert (d^.spanOf) (show $ pretty "Duplicate constructor / destructor") $ uniq $ n : map fst xs
          local (set (inScopeIndices) $ map (\i -> (i, IdxGhost)) is) $
              forM_ xs $ \(x, t) -> do
                  checkTy t
                  assert (d^.spanOf) (show $ pretty x <+> pretty "already defined") $ not $ member x dfs
                  llbl <- tyLenLbl t
                  flowCheck (t^.spanOf) llbl advLbl
          let projs = map (\(x, t) ->  (x, StructProjector n x)) xs 
          local (over (curMod . userFuncs) $ insert n (StructConstructor n)) $ 
              local (over (curMod . userFuncs) $ mappend projs) $ 
                  addTyDef n (StructDef ixs) $ 
                      cont
      (DeclEnum n b) -> do
        (is, bdy) <- unbind b
        local (set (inScopeIndices) $ map (\i -> (i, IdxGhost)) is) $
            mapM_ checkTy $ catMaybes $ map snd bdy
        assert (d^.spanOf) (show $ "Enum " ++ n ++ " must be nonempty") $ length bdy > 0
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
          tbls <- view $ curMod . tableEnv
          locs <- view $ curMod . localities
          assert (d^.spanOf) (show $ pretty "Duplicate table name: " <> pretty n) (not $ member n tbls)
          normLocality (d^.spanOf) loc
          checkTy t
          local (over (curMod . tableEnv) $ insert n (t, loc)) cont
      (DeclDetFunc f opts ar) -> do
        dfs <- view detFuncs
        assert (d^.spanOf) (show $ pretty f <+> pretty "already defined") $ not $ member f dfs
        local (over (curMod . userFuncs) $ insert f (UninterpUserFunc f ar)) $ 
            cont
      (DeclRandOrcl s bnd adm) -> do
        (is, (aes, nts)) <- unbind bnd
        -- assert (d^.spanOf) (show $ pretty "TODO: params") $ length ps == 0
        assert (d^.spanOf) ("Empty random oracle declaration") $ length nts > 0
        local (over inScopeIndices $ mappend $ map (\i -> (i, IdxGhost)) is) $ do
            _ <- mapM inferAExpr aes
            forM_ nts $ \nt -> do
                checkNameType nt
                checkROName nt
            localROCheck (d^.spanOf) aes
            case adm of
              AdmitUniqueness -> return ()
              NoAdmitUniqueness -> checkROUnique (d^.spanOf) aes
            ro <- view $ curMod . randomOracle
            assert (d^.spanOf) (show $ pretty "Duplicate RO lbl: " <> pretty s) $ not $ member s ro
        local (over (curMod . randomOracle) $ insert s bnd) cont 

nameExpIsLocal :: NameExp -> Check Bool
nameExpIsLocal ne = 
    case ne^.val of
      BaseName _ (PRes (PDot p s)) -> do
          p' <- curModName
          return $ p `aeq` p'
      ROName (PRes (PDot p s)) _ i -> do
          p' <- curModName
          return $ p `aeq` p'
      PRFName ne _ -> nameExpIsLocal ne

ensureOnlyLocalNames :: AExpr -> Check ()
ensureOnlyLocalNames ae = do
    case ae^.val of
      AEVar _ _ -> return ()
      AEApp _ _ aes -> forM_ aes ensureOnlyLocalNames
      AEString _ -> return ()
      AEGet n -> do
          b <- nameExpIsLocal n
          assert (ae^.spanOf) "Random oracle decl must only involve local names" b
      AEGetEncPK n -> do
          b <- nameExpIsLocal n
          assert (ae^.spanOf) "Random oracle decl must only involve local names" b
      AEGetVK n -> do
          b <- nameExpIsLocal n
          assert (ae^.spanOf) "Random oracle decl must only involve local names" b
      AEPackIdx _ a -> ensureOnlyLocalNames a
      AELenConst _ -> return ()
      AEInt _ -> return ()

localROCheck :: Ignore Position -> [AExpr] -> Check ()
localROCheck pos aes = laxAssertion $ do
    -- Locality check
    forM_ aes $ ensureOnlyLocalNames
    -- Injectivity check
    ts <- mapM inferAExpr aes
    bs <- forM ts $ \t ->
        case t^.val of
          TName ne -> nameExpIsLocal ne
          TVK ne -> nameExpIsLocal ne
          TDH_PK ne -> nameExpIsLocal ne
          TEnc_PK ne -> nameExpIsLocal ne
          TSS ne ne' -> liftM2 (||) (nameExpIsLocal ne) (nameExpIsLocal ne')
          _ -> return False
    assert pos ("Random oracle decl must involve a local name") $ or bs
    



checkROName :: NameType -> Check ()
checkROName nt =  
    case nt^.val of
      NT_Nonce -> return ()
      NT_Enc _ -> return ()
      NT_MAC _ -> return ()
      _ -> typeError (nt^.spanOf) $ "Bad RO Name: " ++ show (pretty nt)

withAllSplits :: [Prop] -> Check () -> Check ()
withAllSplits [] k = k
withAllSplits (p:ps) k = do
    x <- freshVar
    withVars [(s2n x, (ignore x, tLemma p))] $ do
        (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ mkSpanned PFalse
        if b then return () else withAllSplits ps k
    withVars [(s2n x, (ignore x, tLemma $ pNot p))] $ do
        (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ mkSpanned PFalse
        if b then return () else withAllSplits ps k

-- We then fold the list of decls, checking later ones after processing the
-- earlier ones.
checkDecls :: [Decl] -> Check ()
checkDecls [] = return ()
checkDecls (d:ds) = checkDecl d (checkDecls ds)
--
checkDeclsWithCont :: [Decl] -> Check a -> Check a
checkDeclsWithCont [] k = k
checkDeclsWithCont (d:ds) k = checkDecl d $ checkDeclsWithCont ds k


checkROUnique :: Ignore Position -> [AExpr] -> Check ()
checkROUnique pos es = laxAssertion $ do
    ro_vals <- view $ curMod . randomOracle
    (_, b) <- SMT.smtTypingQuery $ SMT.symROUnique ro_vals es 
    assert pos "RO uniqueness check failed" b
    return ()

checkNameType :: NameType -> Check ()
checkNameType nt =
    case nt^.val of
      NT_DH -> return ()
      NT_Sig t -> checkTy t
      NT_Nonce -> return ()
      NT_PRF xs -> do
          assert (nt^.spanOf) ("PRF value labels not unique") $ uniq $ map fst xs
          forM_ xs (\(_, (a, t)) -> do
              _ <- inferAExpr a
              checkNameType t)
          (_, b) <- SMT.smtTypingQuery $ SMT.symListUniq (map (fst . snd) xs)
          assert (nt^.spanOf) "PRF uniqueness check failed" b
      NT_Enc t -> do
        checkTy t
        debug $ pretty "Checking if type " <> pretty t <> pretty " has public lengths "
        checkTyPubLen t
      NT_EncWithNonce t p np -> do
          checkTy t
          checkTyPubLen t
          checkNoncePattern np
          checkCounter (nt^.spanOf) p
      NT_PKE t -> do
          checkTy t
          checkTyPubLen t
      NT_MAC t -> checkTy t

checkNoncePattern :: NoncePattern -> Check ()
checkNoncePattern NPHere = return ()

checkCounter :: Ignore Position -> Path -> Check ()
checkCounter pos p@(PRes (PDot p0 s)) = do
    p' <- curModName
    assert pos ("Counter must be local: " ++ (show p)) $ p0 `aeq` p'
    md <- openModule pos p0
    case lookup s (md^.ctrEnv) of
      Just _ -> return ()
      Nothing -> typeError pos $ "Unknown counter: " ++ show p


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
checkTy t =
    local (set tcScope $ TcGhost) $
        case t^.val of
          TUnit -> return ()
          TBool l -> checkLabel l
          (TData l1 l2) -> do
              checkLabel l1
              checkLabel l2
              flowCheck (t^.spanOf) l2 l1
          (TDataWithLength l a) -> do
              checkLabel l
              t <- inferAExpr a
              l' <- coveringLabel t
              flowCheck (t^.spanOf) l' l
          (TRefined t xp) -> do
              (x, p) <- unbind xp
              checkTy t
              withVars [(x, (ignore $ show x, t))] $ checkProp p
          (TOption t) -> do
              checkTy t
          (TConst s ps) -> do
              td <- getTyDef (t^.spanOf) s
              forM_ ps checkParam
              case td of
                TyAbstract -> do
                    assert (t^.spanOf) (show $ pretty "Abstract types do not support indices yet") $ length ps == 0
                TyAbbrev t ->
                    assert (t^.spanOf) (show $ pretty "Params should be empty for abbrev " <> pretty s) $ length ps == 0
                StructDef ib -> do
                    _ <- extractStruct (t^.spanOf) ps (show s) ib
                    return ()
                EnumDef b -> do
                    _ <- extractEnum (t^.spanOf) ps (show s) b
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
                _ -> typeError (t^.spanOf) $ show $ ErrWrongNameType n "sig" nt
          (TDH_PK n) -> do
              nt <- getNameType n
              case nt^.val of
                NT_DH -> return ()
                _ -> typeError (t^.spanOf) $ show $  ErrWrongNameType n "DH" nt
          (TEnc_PK n) -> do
              nt <- getNameType n
              case nt^.val of
                NT_PKE _ -> return ()
                _ -> typeError (t^.spanOf) $ show $ ErrWrongNameType n "PKE" nt
          (TSS n m) -> do
              nt <- getNameType n
              nt' <- getNameType m
              case (nt^.val, nt'^.val) of
                (NT_DH, NT_DH) -> return ()
                (NT_DH, _) -> typeError (t^.spanOf) $ show $ ErrWrongNameType n "DH" nt
                (_, NT_DH) -> typeError (t^.spanOf) $ show $ ErrWrongNameType m "DH" nt
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
      TData _ l -> return l
      TDataWithLength _ a -> do
          t <- inferAExpr a
          coveringLabel t
      TRefined t' _ -> tyLenLbl t'
      TOption t' -> do
          l' <- tyLenLbl t'
          return $ joinLbl advLbl l'
      TConst s ps -> do
          td <- getTyDef (t^.spanOf) s
          case td of
            TyAbstract -> return advLbl
            TyAbbrev t -> tyLenLbl t
            StructDef b -> do
                bdy <- extractStruct (t^.spanOf) ps (show s) b
                local (set tcScope $ TcGhost) $ do
                    ls <- forM bdy $ \(_, t) -> tyLenLbl t
                    return $ foldr joinLbl zeroLbl ls
            EnumDef b -> do
                bdy <- extractEnum (t^.spanOf) ps (show s) b
                ls <- forM bdy $ \(_, ot) ->
                    case ot of
                      Just t' -> tyLenLbl t'
                      Nothing -> return zeroLbl
                return $ joinLbl advLbl (foldr joinLbl zeroLbl ls)
      (TCase _ _ _) -> do
          t' <- normalizeTy t
          case t'^.val of
            TCase p _ _ -> do
                debug $ pretty "Got inconclusive prop on TCase"
                typeError (t^.spanOf) $ show $ pretty "Inconclusive: " <> pretty p
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
    flowCheck (ignore def) l advLbl

checkLabel :: Label -> Check ()
checkLabel l =
    local (set tcScope TcGhost) $
        case l^.val of
          (LName n) -> do
              _ <- getNameTypeOpt n
              return ()
          LZero -> return ()
          LAdv -> return ()
          (LJoin l1 l2) -> do
              checkLabel l1
              checkLabel l2
          (LConst (TyLabelVar p))  -> do
              _ <- getTyDef (l^.spanOf) p
              return ()
          (LRangeIdx il) -> do
              (i, l) <- unbind il
              local (over (inScopeIndices) $ insert i IdxGhost) $ checkLabel l

checkProp :: Prop -> Check ()
checkProp p =
    local (set tcScope $ TcGhost) $
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
          (PHappened s (idxs1, idxs2) xs) -> do
              -- TODO: check that method s is in scope?
              _ <- mapM inferAExpr xs
              mapM_ checkIdx idxs1
              mapM_ checkIdx idxs2
              return ()
          (PEq x y) -> do
              _ <- inferAExpr x
              _ <- inferAExpr y
              return ()
          (PEqIdx i1 i2) -> do
              checkIdx i1
              checkIdx i2



flowsTo :: Ignore Position -> Label -> Label -> Check Bool
flowsTo osp l1' l2' = do
    l1 <- normalizeLabel l1'
    l2 <- normalizeLabel l2'
    tyc <- view tyContext
    debug $ pretty "Checking " <> pretty l1 <+> pretty "<=" <+> pretty l2
    (fn, b) <- SMT.checkFlows l1 l2
    return b
    case b of
      Just r -> do
        debug $ pretty "Got " <> pretty b <> pretty " from " <> pretty fn
        return r
      Nothing -> typeError osp $ show $ pretty "Inconclusive: " <> pretty l1 <+> pretty "<=" <+> pretty l2 
      -- <> line <> pretty "Under context: " <> prettyTyContext tyc  <> pretty fn


decideProp :: Prop -> Check (Maybe Bool)
decideProp p = do
    tyc <- view tyContext
    debug $ pretty "Deciding" <+> pretty p
    (fn, r) <- SMT.symDecideProp p
    case r of
      Just b -> debug $ pretty "Got" <+> pretty b <+> pretty " from" <> pretty fn <+> pretty "Under context:" <> prettyTyContext tyc
      Nothing -> debug $ pretty "Inconclusive" <+> pretty " from" <> pretty fn <+> pretty "Under context:" <> prettyTyContext tyc
    return r

flowCheck :: Ignore Position -> Label -> Label -> Check ()
flowCheck sp l1 l2 = laxAssertion $ do
    b <- flowsTo sp l1 l2
    assert sp (show $ ErrFlowCheck l1 l2) b

-- Ensure l flows to LAdv

stripRefinements :: Ty -> Ty
stripRefinements t =
    case t^.val of
      TRefined t _ -> stripRefinements t
      _ -> t


-- TODO: generalize for RO?

stripNameExp :: DataVar -> NameExp -> Check NameExp
stripNameExp x e = return e

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
      PHappened s _ xs -> do
          if x `elem` concat (map getAExprDataVars xs) then return pTrue else return p

stripTy :: DataVar -> Ty -> Check Ty
stripTy x t =
    case t^.val of
      TData l1 l2 -> do
          l1' <- stripLabel x l1
          l2' <- stripLabel x l2
          return $ tData l1' l2'
      TDataWithLength l1 ae -> do
          l' <- stripLabel x l1
          if x `elem` getAExprDataVars ae then return $ tData l' l' else return $ tDataWithLength l' ae
      TRefined t1 yp -> do
          (y, p) <- unbind yp
          t' <- stripTy x t1
          p' <- stripProp x p
          return $ tRefined t' (bind y p')
      TOption t -> do
          t' <- stripTy x t
          return $ mkSpanned $ TOption t'
      TCase p t1 t2 -> do
          assert (t^.spanOf) (show $ pretty "Error on TCase: free variable " <> pretty (show x) <> pretty " should not appear in " <> pretty p) $ (not $ x `elem` getPropDataVars p)
          t1' <- stripTy x t1
          t2' <- stripTy x t2
          return $ mkSpanned $ TCase p t1' t2'
      TConst s ps -> do
          forM_ ps $ \p ->
              case p of
                ParamAExpr a ->
                    if x `elem` getAExprDataVars a then typeError (t^.spanOf) "Hard case for TConst" else return ()
                ParamLbl l ->
                    if x `elem` getLabelDataVars l then typeError (t^.spanOf) "Hard case for TConst" else return ()
                ParamTy t ->
                    if x `elem` getTyDataVars t then typeError (t^.spanOf) "Hard case for TConst" else return ()
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

checkEndpoint :: Ignore Position -> Endpoint -> Check ()
checkEndpoint pos (Endpoint x) = do
    s <- view $ endpointContext
    assert pos (show $ pretty "Unknown endpoint: " <> pretty x) $ elem x s
checkEndpoint pos (EndpointLocality l) = do
    normLocality pos l
    return ()

getOutTy :: Maybe Ty -> Ty -> Check Ty
getOutTy ot t1 = 
    normalizeTy =<< case ot of
      Nothing -> return t1
      Just t2 -> do
          assertSubtype t1 t2
          return t2

-- Infer type for expr
checkExpr :: Maybe Ty -> Expr -> Check Ty
checkExpr ot e = do
    debug $ pretty "Inferring expr " <> pretty e
    case e^.val of
      ECrypt cop aes -> do
          args <- forM aes $ \a -> do
              t <- inferAExpr a
              t' <- normalizeTy t
              return (a, t')
          checkCryptoOp (e^.spanOf) ot cop args
      (EInput xsk) -> do
          ((x, s), k) <- unbind xsk
          withVars [(x, (ignore $ show x, tData advLbl advLbl))] $ local (over (endpointContext) (s :)) $ checkExpr ot k
      (EGetCtr p iargs) -> do 
          checkCounterIsLocal (e^.spanOf) p iargs
          getOutTy ot $ tData advLbl advLbl
      (EIncCtr p iargs) -> do
          checkCounterIsLocal (e^.spanOf) p iargs
          getOutTy ot $ tUnit
      (EOutput a ep) -> do
          case ep of
            Nothing -> return ()
            Just ep -> checkEndpoint (e^.spanOf) ep
          t' <- inferAExpr a
          l_t <- coveringLabel t'
          flowCheck (e^.spanOf) l_t advLbl
          getOutTy ot tUnit
      (EAssert p) -> do
          local (set tcScope $ TcGhost) $ checkProp p
          (fn, b) <- SMT.smtTypingQuery $ SMT.symAssert p
          g <- view tyContext
          debug $ pretty "Type context for assertion " <> pretty p <> pretty ":" <> (prettyTyContext g)
          assert (e^.spanOf) (show $ ErrAssertionFailed fn p) b
          getOutTy ot $ tRefined tUnit (bind (s2n ".x") p)
      (EAssume p) -> do
          local (set tcScope $ TcGhost) $ checkProp p
          getOutTy ot $ tRefined tUnit (bind (s2n ".x") p)
      (EAdmit) -> getOutTy ot $ tAdmit
      (EDebug (DebugPrintModules)) -> do
          ms <- view openModules
          liftIO $ putStrLn $ show ms
          getOutTy ot $ tUnit
      (EDebug (DebugPrint s)) -> do
          liftIO $ putStrLn s
          getOutTy ot $ tUnit
      (EDebug (DebugPrintTyOf a)) -> do
          t <- inferAExpr a
          t' <- normalizeTy t
          e <- ask
          tyc <- view tyContext
          liftIO $ putStrLn $ show $ pretty "Type for " <> pretty a <> pretty ": " <> pretty t <> line <> pretty "Normalized: " <> pretty t' <> line <> pretty "Under context: " <> prettyTyContext tyc
          getOutTy ot $ tUnit
      (EDebug (DebugPrintTy t)) -> do
          t' <- normalizeTy t
          liftIO $ putStrLn $ show $ pretty t <+> pretty "normalizes to: " <> pretty t'
          getOutTy ot $ tUnit
      (EDebug (DebugPrintProp p)) -> do
          liftIO $ putStrLn $ show $ pretty p
          getOutTy ot $ tUnit
      (EDebug (DebugPrintTyContext)) -> do
          tC <- view tyContext
          liftIO $ putStrLn $ show $ prettyTyContext tC
          getOutTy ot $ tUnit
      (EDebug (DebugPrintExpr e)) -> do
          liftIO $ putStrLn $ show $ pretty e
          getOutTy ot $ tUnit
      (EDebug (DebugPrintLabel l)) -> do
          liftIO $ putStrLn $ show $ pretty l
          getOutTy ot $ tUnit
      (EUnionCase a xe) -> do
          t <- inferAExpr a
          (x, e) <- unbind xe
          case (stripRefinements t)^.val of
            TUnion t1 t2 -> do
                debug $ pretty "first case for EUnionCase"
                t1' <- withVars [(x, (ignore $ show x, t1))] $ checkExpr ot e
                debug $ pretty "first case got" <+> pretty t1'
                debug $ pretty "second case for EUnionCase"
                t2' <- withVars [(x, (ignore $ show x, t2))] $ checkExpr ot e
                debug $ pretty "second case got" <+> pretty t2'
                assertSubtype t1' t2'
                getOutTy ot =<< stripTy x t2'
            _ -> do  -- Just continue
                t <- withVars [(x, (ignore $ show x, t))] $ checkExpr ot e
                getOutTy ot =<< stripTy x t
      (ELet e tyAnn sx xe') -> do
          case tyAnn of
            Just t -> checkTy t
            Nothing -> return ()
          t1 <- checkExpr tyAnn e
          (x, e') <- unbind xe'
          t2 <- withVars [(x, (ignore sx, t1))] (checkExpr ot e')
          stripTy x t2
      (EChooseIdx ip ik) -> do
          (_, b) <- SMT.symDecideProp $ mkSpanned $ PQuantIdx Exists ip
          (i, k) <- unbind ik
          case b of
            Just True -> do
                (ix, p) <- unbind ip
                x <- freshVar
                let tx = tLemma (subst ix (mkIVar i) p) 
                to <- local (over inScopeIndices $ insert i IdxGhost) $ do
                    withVars [(s2n x, (ignore x, tx))] $ checkExpr ot k
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
          case (stripRefinements t)^.val of
            TExistsIdx jt' -> do
                (j, t') <- unbind jt'
                let tx = tRefined (subst j (mkIVar i) t') (bind (s2n ".res") (pEq (aeVar ".res") a) )
                to <- local (over (inScopeIndices) $ insert i IdxGhost) $ do
                    withVars [(x, (ignore $ show x, tx))] $ checkExpr ot e
                to' <- stripTy x to
                if i `elem` getTyIdxVars to' then
                    return (tExistsIdx (bind i to'))
                else return to'
            _ -> do
                t' <- local (over (inScopeIndices) $ insert i IdxGhost) $ withVars [(x, (ignore $ show x, t))] $ checkExpr ot e
                to' <- stripTy x t'
                if i `elem` getTyIdxVars to' then
                    return (tExistsIdx (bind i to'))
                else return to'
      (ETLookup pth@(PRes (PDot p n)) a) -> do
          md <- openModule (e^.spanOf) p
          case lookup n (md^.tableEnv) of 
            Nothing -> typeError (e^.spanOf) $ show $ pretty (unignore $ a^.spanOf) <+> pretty "Unknown table: " <> pretty n
            Just (t, loc) -> do
                tc <- view tcScope
                ta <- inferAExpr a
                assertSubtype ta (tData advLbl advLbl)
                case tc of
                  TcDef curr_loc -> do
                      curr_loc' <- normLocality (e^.spanOf) curr_loc
                      loc' <- normLocality (e^.spanOf) loc
                      assert (e^.spanOf) (show $ pretty "Wrong locality for table: got" <> pretty curr_loc <+> pretty "but expected" <+> pretty loc) $ curr_loc' `aeq` loc'
                      getOutTy ot $ mkSpanned $ TOption t
                  _ -> typeError (e^.spanOf) $ "Weird case: should be in a def"
      (ETWrite pth@(PRes (PDot p n)) a1 a2) -> do
          md <- openModule (e^.spanOf) p
          case lookup n (md^.tableEnv) of 
            Nothing -> typeError (e^.spanOf) $ show $  pretty (unignore $ e^.spanOf) <+> pretty "Unknown table: " <> pretty n
            Just (t, loc) -> do
                tc <- view tcScope
                case tc of
                  TcDef curr_loc -> do
                      curr_loc' <- normLocality (e^.spanOf) curr_loc
                      loc' <- normLocality (e^.spanOf) loc
                      assert (e^.spanOf) (show $ pretty "Wrong locality for table: got" <> pretty curr_loc <+> pretty "but expected" <+> pretty loc) $ curr_loc' `aeq` loc'
                      ta <- inferAExpr a1
                      assertSubtype ta (tData advLbl advLbl)
                      ta2 <- inferAExpr a2
                      assertSubtype ta2 t
                      getOutTy ot $ tUnit

      (ECall f (is1, is2) args) -> do
          bfdef <- getDefSpec (e^.spanOf) f
          ts <- view tcScope
          ((bi1, bi2), dspec) <- unbind bfdef
          assert (e^.spanOf) (show $ pretty "Wrong index arity for " <> pretty f) $ length is1 == length bi1
          assert (e^.spanOf) (show $ pretty "Wrong index arity for " <> pretty f) $ length is2 == length bi2
          forM_ is1 checkIdxSession
          forM_ is2 checkIdxPId
          let (DefSpec _ fl o) = substs (zip bi1 is1) $ substs (zip bi2 is2) dspec
          case ts of
            TcDef curr_locality -> do
                fl' <- normLocality (e^.spanOf) fl
                curr_locality' <- normLocality (e^.spanOf) curr_locality
                assert (e^.spanOf) (show $ pretty "Wrong locality for function call") $ fl' `aeq` curr_locality'
                (xts, (pr, rt, _)) <- unbind o
                assert (e^.spanOf) (show $ pretty "Wrong variable arity for " <> pretty f) $ length args == length xts
                argTys <- mapM inferAExpr args
                forM (zip xts argTys) $ \((_, t), t') -> assertSubtype t' (unembed t)
                let (prereq, retTy) = substs (zip (map fst xts) args) (pr, rt)
                (fn, b) <- SMT.smtTypingQuery $ SMT.symAssert prereq
                assert (e^.spanOf) ("Precondition failed: " ++ show (pretty prereq) ++ show (pretty fn)) b
                let happenedProp = pHappened f (is1, is2) args
                getOutTy ot $ (tRefined retTy (bind (s2n ".res") happenedProp))
            _ -> typeError (ignore def ) $ "Unreachable"
      (EIf a e1 e2) -> do
          debug $ pretty "Checking if at" <+> pretty (unignore $ e^.spanOf)
          t <- inferAExpr a
          lt <- coveringLabel t
          flowCheck (a^.spanOf) lt advLbl
          -- debug $ pretty "\t" <> pretty t <> pretty "\t" <> pretty (subst (s2n ".res") (aeVar ".pCond") t)
          -- Carry forward refinements from t into the path condition
          t' <- normalizeTy t
          pathRefinement <- case t' ^. val of
            TRefined _ xp -> do
                (x, p) <- unbind xp
                return $ subst x a p 
            _ -> return pTrue
          x <- freshVar
          t1 <- withVars [(s2n x, (ignore x, tRefined tUnit (bind (s2n ".pCond") $ pAnd (pEq a aeTrue) pathRefinement)))] $ checkExpr ot e1
          t2 <- withVars [(s2n x, (ignore x, tRefined tUnit (bind (s2n ".pCond") $ pAnd (pNot $ pEq a aeTrue) pathRefinement)))] $ checkExpr ot e2
          case ot of 
            Just t3 -> return t3
            Nothing -> do
                t1' <- stripTy (s2n x) t1
                assertSubtype t2 t1'
                return t1'
      (ERet a) -> do
          t <- inferAExpr a
          getOutTy ot $ tRefined t (bind (s2n ".res") $ pEq (aeVar ".res") a)
      (EFalseElim e) -> do
        (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ mkSpanned PFalse
        if b then getOutTy ot tAdmit else checkExpr ot e
      (EPCase p e) -> do
          _ <- local (set tcScope TcGhost) $ checkProp p
          x <- freshVar
          t1 <- withVars [(s2n x, (ignore x, tLemma p))] $ do
              (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ mkSpanned PFalse
              if b then getOutTy ot tAdmit else checkExpr ot e
          t2 <- withVars [(s2n x, (ignore x, tLemma (pNot p)))] $ do
              (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ mkSpanned PFalse
              if b then getOutTy ot tAdmit else checkExpr ot e
          return $ mkSpanned $ TCase p t1 t2
      (ECase e1 cases) -> do
          debug $ pretty "Typing checking case: " <> pretty (unignore $ e^.spanOf)
          t <- checkExpr Nothing e1
          debug $ pretty "Inferred type " <> pretty t <> pretty "for argument"
          t <- normalizeTy t
          let t' = stripRefinements t
          (l, otcases) <- case t'^.val of
                            TData l1 l2 -> return (l1, Left (tData l1 l2))
                            TOption to -> return (advLbl, Right $ [("Some", Just to), ("None", Nothing)])
                            TConst s ps -> do
                                td <- getTyDef (t^.spanOf) s
                                case td of
                                  EnumDef b -> do
                                      bdy <- extractEnum (t'^.spanOf) ps (show s) b
                                      return (advLbl, Right bdy)
          assert (e^.spanOf) (show $ pretty "Empty cases on case expression") $ length cases > 0
          flowCheck (e1^.spanOf) l advLbl
          branch_tys <- 
              case otcases of
                Left td -> do
                    forM cases $ \(c, ocase) -> 
                        case ocase of
                          Left e -> checkExpr ot e
                          Right (sb, xe) -> do
                              (x, e) <- unbind xe
                              t <- withVars [(x, (sb, td))] $ checkExpr ot e
                              case ot of
                                 Just _ -> return t
                                 Nothing -> stripTy x t
                Right tcases -> do
                    forM tcases $ \(c, ot') ->
                        case (ot', lookup c cases) of
                          (_, Nothing) -> typeError (e^.spanOf) $ show $ pretty "Case not found: " <> pretty c
                          (Nothing, Just (Left e)) -> checkExpr ot e
                          (Just tc, Just (Right (sb, xe))) -> do
                              (x, e) <- unbind xe
                              t <- withVars [(x, (sb, tc))] $ checkExpr ot e
                              case ot of
                                Just _ -> return t
                                Nothing -> stripTy x t
                          (_, _) -> typeError (e^.spanOf) $ show $ pretty "Mismatch on case: " <> pretty c
          case ot of
            Just t -> return t
            Nothing -> do -- Need to synthesize type here. Take the first one
                let t = head branch_tys
                forM_ (tail branch_tys) $ \t' -> assertSubtype t' t
                return t

data EncKeyKind = 
    AEnc
    | AEnc_Ctr
    deriving Eq
   

doAEnc encKeyKind pos t1 x t args =
  case extractNameFromType t1 of
    Just k -> do
        nt <- local (set tcScope TcGhost) $  getNameType k
        case nt^.val of
          NT_EncWithNonce t' _ _ | encKeyKind == AEnc_Ctr -> do
              debug $ pretty "Checking encryption for " <> pretty k <> pretty " and " <> pretty t
              b1 <- isSubtype t t'
              if b1 then
                  return $ mkSpanned $ TRefined (tData zeroLbl zeroLbl) $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (aeApp (topLevelPath $ "cipherlen") [] [aeLength x])
              else
                  mkSpanned <$> trivialTypeOf [t1, t]
          NT_Enc t' | encKeyKind == AEnc -> do
              debug $ pretty "Checking encryption for " <> pretty k <> pretty " and " <> pretty t
              b1 <- isSubtype t t'
              if b1 then
                  return $ mkSpanned $ TRefined (tData zeroLbl zeroLbl) $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (aeApp (topLevelPath $ "cipherlen") [] [aeLength x])
              else
                  mkSpanned <$> trivialTypeOf [t1, t]
          _ -> typeError (ignore def) $ show $ ErrWrongNameType k "encryption key" nt
    _ -> do
        debug $ pretty "Got extremely wrong case: " <> pretty args
        mkSpanned <$> trivialTypeOf [t1, t]

doADec encKeyKind pos t1 t args = 
    case extractNameFromType t1 of
      Just k -> do
          debug $ pretty "Trying nontrivial dec"
          nt <-  local (set tcScope TcGhost) $ getNameType k
          l <- coveringLabel t
          case nt^.val of
            NT_EncWithNonce t' _ _ | encKeyKind == AEnc_Ctr -> do 
                b2 <- flowsTo (ignore def) (nameLbl k) advLbl
                if ((not b2)) then do
                    -- Honest
                    debug $ pretty "Honest dec"
                    return $ mkSpanned $ TOption t'
                else do
                    debug $ pretty "Corrupt dec"
                    -- Corrupt
                    let l_corr = joinLbl (nameLbl k) l
                    debug $ pretty "joinLbl succeeded"
                    return $ tData l_corr l_corr -- Change here
            NT_Enc t' | encKeyKind == AEnc -> do
                b2 <- flowsTo (ignore def) (nameLbl k) advLbl
                if ((not b2)) then do
                    -- Honest
                    debug $ pretty "Honest dec"
                    return $ mkSpanned $ TOption t'
                else do
                    debug $ pretty "Corrupt dec"
                    -- Corrupt
                    let l_corr = joinLbl (nameLbl k) l
                    debug $ pretty "joinLbl succeeded"
                    return $ tData l_corr l_corr -- Change here
            _ -> typeError (ignore def) $ show $  ErrWrongNameType k "encryption key" nt
      _ -> do
          l <- coveringLabelOf [t1, t]
          debug $ pretty "Trivial dec"
          return $ tData l l -- Change here

prettyMaybe :: Pretty a => Maybe a -> Doc ann
prettyMaybe x = 
    case x of
      Nothing -> pretty "Nothing"
      Just x -> pretty "Just" <+> pretty x

checkCryptoOp :: Ignore Position -> Maybe Ty -> CryptOp -> [(AExpr, Ty)] -> Check Ty
checkCryptoOp pos ot cop args = do
    debug $ pretty $ "checkCryptoOp:" ++ show (pretty cop) ++ " " ++ show (pretty args)
    case cop of
      CHash p is i -> do                            
          local (set tcScope TcGhost) $ forM_ is checkIdx
          let aes = map fst args
          bnd <- getRO pos p
          (ixs, (aes'_, nts_)) <- unbind bnd
          assert pos ("RO index out of bounds") $ i < length nts_
          assert pos ("Wrong index arity for RO") $ length is == length ixs
          let aes' = substs (zip ixs is) aes'_
          let nts = substs (zip ixs is) nts_
          debug $ pretty $ "Trying to prove if " ++ show (pretty aes) ++ " equals " ++ show (pretty aes')
          (_, b_eq) <- SMT.smtTypingQuery $ SMT.symCheckEqTopLevel aes' aes
          uns <- unsolvability aes'
          b <- decideProp uns
          debug $ pretty "Decision result for hash: " 
          debug $ pretty "equals expected hash:" <+> pretty b_eq
          debug $ pretty "unsolvability:" <+> prettyMaybe b
          case (b_eq, b) of
            (True, Just True) -> getOutTy ot $ mkSpanned $ TName $ roName p is i
            _ -> do 
                noCollision <- SMT.symDecideNotInRO aes
                if noCollision then 
                    getOutTy ot $ mkSpanned $ TData advLbl advLbl
                else do 
                    let ts = map snd args
                    forM_ ts $ \t -> tyFlowsTo t advLbl
                    getOutTy ot $ mkSpanned $ TData advLbl advLbl
      CPRF s -> do
          assert pos ("Wrong number of arguments to prf") $ length args == 2
          let [(_, t1), (a, t)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just k -> do
                nt <-  local (set tcScope TcGhost) $ getNameType k
                case nt^.val of
                  NT_PRF aes -> do
                      case L.find (\p -> fst p == s) aes of
                        Nothing -> typeError pos $ "Unknown PRF label: " ++ s
                        Just (_, (ae, nt')) -> do
                            (_, b) <- SMT.smtTypingQuery $ SMT.symCheckEqTopLevel [ae] [a]
                            corr <- flowsTo (ignore def) (nameLbl k) advLbl
                            if (not corr) && b then return (mkSpanned $ TName $ prfName k s) else mkSpanned <$> trivialTypeOf [t1, t]
                  _ -> typeError pos $ "Wrong name type for PRF"
      CAEnc -> do
          assert pos ("Wrong number of arguments to encryption") $ length args == 2
          let [(_, t1), (x, t)] = args
          doAEnc AEnc pos t1 x t args
      CADec -> do 
          assert pos ("Wrong number of arguments to decryption") $ length args == 2
          let [(_, t1), (_, t)] = args
          doADec AEnc pos t1 t args
      CAEncWithNonce p iargs -> do
          checkCounterIsLocal pos p iargs
          assert pos ("Wrong number of arguments to encryption") $ length args == 2
          let [(_, t1), (x, t)] = args
          doAEnc AEnc_Ctr pos t1 x t args
      CADecWithNonce -> do 
          assert pos ("Wrong number of arguments to decryption") $ length args == 3
          let [(_, t1), (_, tnonce), (_, t)] = args
          assertSubtype tnonce $ tData advLbl advLbl
          doADec AEnc_Ctr pos t1 t args
      CPKDec -> do 
          assert pos ("Wrong number of arguments to pk decryption") $ length args == 2
          let [(_, t1), (_, t)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just k -> do
              nt <- local (set tcScope TcGhost) $  getNameType k
              case nt^.val of
                NT_PKE t' -> do
                    l <- coveringLabel t
                    b1 <- flowsTo (ignore def) l advLbl
                    b2 <- flowsTo (ignore def) (nameLbl k) advLbl
                    if b1 && (not b2) then do
                        -- TODO HIGH PRIORITY: is this complete?
                        return $ mkSpanned $ TData advLbl advLbl -- TUnion t' (tData advLbl advLbl), 
                    else do
                        let l_corr = joinLbl (nameLbl k) l
                        return $ mkSpanned $ TData l_corr l_corr
      CPKEnc -> do 
          assert pos ("Wrong number of arguments to pk encryption") $ length args == 2
          let [(_, t1), (x, t)] = args
          case extractEncPKFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just k -> do
                nt <- local (set tcScope TcGhost) $  getNameType k
                case nt^.val of
                  NT_PKE t' -> do
                      b <- isSubtype t t'
                      if (b) then
                          return $ mkSpanned $ TRefined (tData zeroLbl zeroLbl) $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (aeApp (topLevelPath $ "pk_cipherlen") [] [aeLength x])
                      else
                          mkSpanned <$> trivialTypeOf [t1, t] 
                  _ -> typeError (ignore def) $ show $ ErrWrongNameType k "encryption key" nt
      CMac -> do
          assert pos ("Wrong number of arguments to mac") $ length args == 2
          let [(_, t1), (_, t)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just k -> do 
                nt <-  local (set tcScope TcGhost) $ getNameType k
                case nt^.val of
                  NT_MAC t' -> do
                      assertSubtype t t'
                      l <- coveringLabel t'
                      return $ mkSpanned $ TRefined (tData l zeroLbl) $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (mkSpanned $ AELenConst "maclen")
                  _ -> mkSpanned <$> trivialTypeOf [t1, t]
      CMacVrfy -> do
          assert pos ("Wrong number of arguments to mac_vrfy") $ length args == 3
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
                      b1 <- flowsTo (ignore def) l1 advLbl
                      b2 <- flowsTo (ignore def) l2 advLbl
                      b3 <- flowsTo (ignore def) (nameLbl k) advLbl
                      if (b1 && b2 && (not b3)) then
                        return $ mkSpanned $ TOption (tRefined t' $ bind (s2n ".res") (pEq (aeVar ".res") m))
                      else
                        let l_corr = joinLbl (nameLbl k) (joinLbl l1 l2) in
                        return $ mkSpanned $ (TData l_corr l_corr) -- Change here
      CSign -> do
          assert pos ("Wrong number of arguments to sign") $ length args == 2
          let [(_, t1), (_, t)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t]
            Just sk -> do
                nt <- local (set tcScope TcGhost) $  getNameType sk
                case nt^.val of
                  NT_Sig t' -> do
                      assertSubtype t t'
                      l <- coveringLabel t'
                      return $ mkSpanned $ TRefined (tData l zeroLbl) $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (mkSpanned $ AELenConst "signature")
                  _ -> mkSpanned <$> trivialTypeOf [t1, t]
      CSigVrfy -> do
          assert pos ("Wrong number of arguments to vrfy") $ length args == 3
          let [(_, t1), (_, x), (_, t)] = args
          case extractVKFromType t1 of
            Nothing -> do
                l <- coveringLabelOf [t1, x, t]
                return $ mkSpanned $ TData l l -- Change here
            Just k -> do 
                nt <-  local (set tcScope TcGhost) $ getNameType k
                case nt^.val of
                  NT_Sig t' -> do
                      debug $ pretty "Checking vrfy: " <> pretty args
                      l1 <- coveringLabel x
                      l2 <- coveringLabel t
                      b1 <- flowsTo (ignore def) l1 advLbl
                      b2 <- flowsTo (ignore def) l2 advLbl
                      b3 <- flowsTo (ignore def) (nameLbl k) advLbl
                      if (b1 && b2 && (not b3)) then return (mkSpanned $ TOption t')
                                                else do
                                                 let l_corr = joinLbl (nameLbl k) (joinLbl l1 l2)
                                                 return $ mkSpanned $ (TData l_corr l_corr) -- Change here
                  _ -> typeError (ignore def) $ show $ ErrWrongNameType k "sig" nt

unsolvability :: [AExpr] -> Check Prop
unsolvability aes = local (set tcScope TcGhost) $ do
    bs <- forM aes $ \ae -> 
        case ae^.val of
          AEApp f _ [x, y] | f `aeq` (topLevelPath $ "dh_combine")-> do
              t1 <- inferAExpr x
              t2 <- inferAExpr y
              case (t1^.val, t2^.val) of
                (TDH_PK n, TName m) -> return $ pAnd (pNot $ pFlow (nameLbl n) advLbl) (pNot $ pFlow (nameLbl m) advLbl)
                _ -> return pFalse
          _ -> do
              t <- inferAExpr ae
              case t^.val of
                TName n -> return $ pNot $ pFlow (nameLbl n) advLbl
                _ -> return pFalse
    return $ foldr pOr pFalse bs

---- Entry point ----

typeCheckDecls :: Flags -> [Decl] -> IO (Either Env Env)
typeCheckDecls f ds = do
    e <- emptyEnv f
    r <- PR.runResolve f $ PR.resolveDecls ds
    case r of
      Left () -> return $ Left e
      Right ds' -> do
          runExceptT $ runReaderT (unCheck $ checkDeclsWithCont ds' $ ask) e


---- Module stuff ----

instance Pretty a => Pretty (Ignore a) where
    pretty x = pretty (unignore x)

defMatches :: Ignore Position -> String -> Maybe Def -> Def -> Check ()
defMatches pos s d1 d2 = 
    case (d1, d2) of
      (Just (DefHeader bl), DefHeader bl') -> assert pos ("Def mismatch with headers: " ++ s) $ bl `aeq` bl'
      (Just (DefHeader bl), Def blspec) -> do
          (is, DefSpec _ l _) <- unbind blspec
          assert pos ("Def mismatch: " ++ s) $ bl `aeq` (bind is l)
      (Just (Def blspec), Def blspec') -> do
          (is1, DefSpec ab l1 pty) <- unbind blspec
          (is', DefSpec ab' l1' pty') <- unbind blspec'
          assert pos ("Def abstractness mismatch: " ++ s) $ (not (unignore ab)) || (unignore ab') -- ab ==> ab'
          (args, (pr1, t1, _)) <- unbind pty
          (args', (pr2, t2, _)) <- unbind pty'
          assert pos ("Def locality mismatch") $ (bind is1 l1) `aeq` (bind is' l1')
          assert pos ("Def prereq mismatch") $ (bind is1 $ bind args pr1) `aeq` (bind is' $ bind args' pr2)
          assert pos ("Def return ty mismatch") $ (bind is1 $ bind args t1) `aeq` (bind is' $ bind args' t2)
      (Nothing, _) -> typeError pos $ "Missing def: " ++ s

tyDefMatches :: Ignore Position -> String -> TyDef -> TyDef -> Check ()
tyDefMatches pos s td1 td2 = 
    case (td1, td2) of
      (EnumDef d1, EnumDef d2) -> assert pos ("Enum mismatch: " ++ s) $ d1 `aeq` d2
      (StructDef d1, StructDef d2) -> assert pos ("Struct mismatch: " ++ s) $ d1 `aeq` d2
      _ -> typeError pos $ "UNIMP: tyDefMatches"


userFuncMatches :: Ignore Position -> String -> UserFunc -> UserFunc -> Check ()
userFuncMatches pos s f1 f2 = assert pos ("Func mismatch: " ++ s) $ f1 == f2

nameMatches :: Ignore Position -> String -> 
    Bind ([IdxVar], [IdxVar]) (Maybe (NameType, [Locality])) -> 
    Bind ([IdxVar], [IdxVar]) (Maybe (NameType, [Locality])) -> 
    Check ()
nameMatches pos s xn1 xn2 = do
    ((is1, is2), on1) <- unbind xn1
    ((is1', is2'), on2) <- unbind xn2
    case (substs (zip is1 (map mkIVar is1')) $ substs (zip is2 (map mkIVar is2')) $ on1, on2) of
      (_, Nothing) -> assert pos ("Arity mismatch for " ++ s) $ (length is1 == length is1') && (length is2 == length is2')
      (Nothing, Just _) -> typeError pos $ "Name should be concrete: " ++ show s
      (Just (nt1, ls1), Just (nt2, ls2)) -> do
          assert pos ("Name type mismatch on name " ++ s) $ nt1 `aeq` nt2
          assert pos ("Locality mismatch on name " ++ s) $ ls1 `aeq` ls2


moduleMatches :: Ignore Position -> ModDef -> ModDef -> Check ()
moduleMatches pos md1 md2 = 
    case (md1, md2) of 
      (MAlias p, _) -> do
          d <- getModDef pos p
          moduleMatches pos d md2
      (_, MAlias p) -> do
          d <- getModDef pos p
          moduleMatches pos md1 d 
      (MBody _, MFun _ _ _) -> typeError pos $ "Expected functor, but got module"
      (MFun _ _ _, MBody _) -> typeError pos $ "Expected module, but got functor"
      (MFun s t1 xmd1, MFun _ t2 ymd2) -> do
          debug $ pretty "Checking moduleMatches of arguments"
          moduleMatches pos t2 t1
          debug $ pretty "Checking moduleMatches of body"
          (x, md1) <- unbind xmd1
          (y, md2_) <- unbind ymd2
          let md2 = subst y (PPathVar (ClosedPathVar $ ignore $ show x) x) md2_
          p <- curModName
          local (over modContext $ insert x t1) $ 
                moduleMatches pos md1 md2
      (MBody xmd1, MBody ymd2) -> do
          (x, md1) <- unbind xmd1
          (y, md2_) <- unbind ymd2
          debug $ pretty "moduleMatches with " <> pretty x <> pretty " and " <> pretty y
          let md2 = subst y (PPathVar OpenPathVar x) md2_
          -- Localities
          forM_ (md2^.localities) $ \(s, i) -> do
              ar1 <- case i of
                       Left ar -> return ar
                       Right p -> normLocalityPath pos $ PRes p 
              ar2 <- case lookup s (md1^.localities) of
                       Nothing -> typeError pos $ "Locality not found for module match: " ++ s
                       Just (Left ar) -> return ar
                       Just (Right p) -> normLocalityPath pos $ PRes p
              assert pos ("Locality arity mismatch for module match: " ++ s) $ ar1 == ar2
          -- Defs
          forM_ (md2^.defs) $ \(s, df) -> defMatches pos s (lookup s (md1^.defs)) df
          -- TableEnv
          forM_ (md2^.tableEnv) $ \(s, tl) -> 
              case lookup s (md1^.tableEnv) of
                Nothing -> typeError pos $ "Missing tenv: " ++ s
                Just tl' -> assert pos ("Table mismatch for " ++ s) $ tl `aeq` tl'
          -- flowAxioms 
          forM_ (md2^.flowAxioms) $ \ax -> 
              case L.find (aeq ax) (md1^.flowAxioms) of 
                Nothing -> typeError pos $ "flow axiom mismatch " ++ show (pretty ax)
                Just _ -> return ()
          -- advCorrConstraints 
          forM_ (md2^.advCorrConstraints) $ \ax -> 
              case L.find (aeq ax) (md1^.advCorrConstraints) of 
                Nothing -> typeError pos $ "corr constraint mismatch " ++ show (pretty ax)
                Just _ -> return ()
          -- tyDefs 
          forM_ (md2^.tyDefs) $ \(s, td) -> 
              case lookup s (md1^.tyDefs) of
                Nothing -> typeError pos $ "Type missing: " ++ s
                Just td' -> tyDefMatches pos s td' td
          -- userFuncs
          forM_ (md2^.userFuncs) $ \(s, f) -> 
              case lookup s (md1^.userFuncs) of
                Nothing -> typeError pos $ "Func missing: " ++ s
                Just f' -> userFuncMatches pos s f' f
          -- nameEnv
          forM_ (md2^.nameEnv) $ \(s, n) -> 
              case lookup s (md1^.nameEnv) of 
                Nothing -> typeError pos $ "Name missing: " ++ s
                Just n' -> nameMatches pos s n' n
          -- modules
          forM_ (md2^.modules) $ \(s, m1) ->
              case lookup s (md1^.modules) of
                Nothing -> typeError pos $ "Module missing: " ++ s
                Just m2 -> moduleMatches pos m2 m1 

--moduleMatches :: Ignore Position -> Bind (Name ResolvedPath) ModDef -> Bind (Name ResolvedPath) ModDef -> Check ()
--moduleMatches pos xmd1 ymd2 = do








