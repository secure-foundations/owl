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

type Check = Check' SMT.SolverEnv

emptyModBody :: IsModuleType -> ModBody
emptyModBody t = ModBody t mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty 

doAssertFalse :: Check Bool
doAssertFalse = do
       (_, b) <- SMT.smtTypingQuery "false_elim" $ SMT.symAssert $ mkSpanned PFalse
       return b

-- extend with new parts of Env -- ok
emptyEnv :: Flags -> IO (Env SMT.SolverEnv)
emptyEnv f = do
    r <- newIORef 0
    r'' <- newIORef 0
    m <- newIORef $ M.empty
    rs <- newIORef []
    memo <- mkMemoEntry 
    gsetup <- newIORef Nothing
    slots <- newIORef $ f^.fParallelizeSplits
    return $ Env mempty mempty mempty Nothing f initDetFuncs (TcGhost False) mempty [(Nothing, emptyModBody ModConcrete)] mempty 
        interpUserFunc r slots m [memo] gsetup mempty rs 0 r'' Nothing (typeError') checkNameType normalizeTy normalizeProp decideProp Nothing Nothing [] False False def


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

trivialTypeOfAnn :: String -> [Ty] -> Check TyX
trivialTypeOfAnn s ts = do
    l <- coveringLabelOf ts
    return $ TData l l (ignore $ Just s)

trivialTypeOfWithLength :: [Ty] -> AExpr -> Check TyX
trivialTypeOfWithLength ts ae = do
    t <- trivialTypeOf ts
    return $ TRefined (mkSpanned t) ".res" $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) ae

checkPublicArguments :: String -> [Ty] -> Check ()
checkPublicArguments errmsg ts = do
    forM_ ts $ \t -> do
        b <- tyFlowsTo t advLbl
        assert errmsg b

enforcePublicArguments :: String -> [Ty] -> Check TyX
enforcePublicArguments errmsg ts = do
    checkPublicArguments errmsg ts
    return $ TData advLbl advLbl (ignore $ Nothing)

enforcePublicArgumentsOption :: String -> [Ty] -> Check TyX
enforcePublicArgumentsOption errmsg ts = do
    checkPublicArguments errmsg ts
    return $ TOption $ tData advLbl advLbl



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

extractKEMPKFromType :: Ty -> Maybe NameExp
extractKEMPKFromType t =
    case (stripRefinements t)^.val of
      TKEM_PK k -> Just k
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

tPubGroupElem :: Ty
tPubGroupElem = tRefined (tData advLbl advLbl) ".res" $ pEq (builtinFunc "is_group_elem" [aeVar ".res"]) (builtinFunc "true" [])

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
    mkSimpleFunc "Some?" 1 $ \args -> 
            case args of
            [t] -> 
                case (stripRefinements t)^.val of
                    TOption t' -> return $ TBool advLbl
                    _ -> do
                        l <- coveringLabel t
                        return $ TBool l
            _ -> typeError $ show $ ErrBadArgs "Some?" args,
    mkSimpleFunc "None?" 1 $ \args -> 
            case args of
            [t] -> 
                case (stripRefinements t)^.val of
                    TOption t' -> return $ TBool advLbl
                    _ -> do
                        l <- coveringLabel t
                        return $ TBool l
            _ -> typeError $ show $ ErrBadArgs "None?" args,
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
    mkSimpleFunc "concat" 2 $ \args -> trivialTypeOf args, 
    mkSimpleFunc "xor" 2 $ \args -> trivialTypeOf args, 
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
    mkSimpleFunc "kem_pk" 1 $ \args ->
        case args of
          [t] | Just n <- extractNameFromType t -> do
              nt <-  local (set tcScope (TcGhost False)) $ getNameType n
              case nt^.val of
                NT_KEM _ -> return $ TKEM_PK n
                _ -> trivialTypeOf args
          _ -> trivialTypeOf args,
    ("dh_combine", (2, \ps args ->
        case (ps, args) of
          ([], [(_, t1), (_, t2)]) | Just n <- extractDHPKFromType t1, Just m <- extractNameFromType t2 -> do
              nt_n <-  local (set tcScope $ TcGhost False) $ getNameType n
              nt_m <-  local (set tcScope $ TcGhost False) $ getNameType m
              case (nt_n^.val, nt_m^.val) of
                (NT_DH, NT_DH) -> 
                        return $ TCase (pFlow (nameLbl n) advLbl) tPubGroupElem 
                                                                  (mkSpanned $ TCase (pFlow (nameLbl m) advLbl) tPubGroupElem
                                                                                                                (mkSpanned $ TSS n m))
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
                        return $ TRefined (mkSpanned $ TBool zeroLbl) ".res" $ bind (s2n ".res") $
                            pImpl (pEq (aeVar ".res") (aeApp (topLevelPath "true") [] []))
                                  (pEq (aeGet n) (aeGet m))
                (TName n, m) -> do
                  nt <-  local (set tcScope $ TcGhost False) $ getNameType n
                  case nt^.val of
                    NT_Nonce _ -> do
                        -- TODO: enforce that m's length label is public 
                        l <- coveringLabel (mkSpanned m)
                        return $ TRefined (mkSpanned $ TBool l) ".res" (bind (s2n ".res") (pImpl (pEq (aeVar ".res") (aeApp (topLevelPath $ "true") [] [])) (pAnd (pFlow (nameLbl n) l) (pEq x y))))
                    _ -> trivialTypeOf $ map snd args
                (m, TName n) -> do
                  nt <-  local (set tcScope $ TcGhost False) $ getNameType n
                  case nt^.val of
                    NT_Nonce _ -> do
                        l <- coveringLabel (mkSpanned m)
                        return $ TRefined (mkSpanned $ TBool l) ".res" (bind (s2n ".res") (pImpl (pEq (aeVar ".res") (aeApp (topLevelPath $ "true") [] [])) (pAnd (pFlow (nameLbl n) l) (pEq x y))))
                    _ -> trivialTypeOf $ map snd args
                _ -> do
                  l <- coveringLabelOf $ map snd args
                  return $ TBool l
          _ -> typeError $ "Wrong parameters to checknonce"
    ))
    ]



mkStructType :: ResolvedPath -> TyVar -> [(AExpr, Ty)] -> [Ty] -> [FuncParam] ->  Bind [IdxVar] (DepBind ()) -> Check TyX
mkStructType pth tv args outTs ps b = do
    (is, dp) <- unbind b
    idxs <- getStructParams ps
    assert (show $ owlpretty "Wrong index arity for struct" <+> owlpretty pth <> owlpretty "." <> owlpretty (PRes $ PDot pth tv)) $ length idxs == length is
    let p = map (\(a, s) -> pEq a $ mkSpanned $ AEApp (PRes $ PDot pth s) ps [aeVar ".res"])
                (zip (map fst args) (depBindNames $ substs (zip is idxs) dp))
    slengths <- sumOfLengths (zip (map fst args) outTs)
    return $ TRefined (mkSpanned $ TConst (PRes $ PDot pth tv) ps) ".res" $
        bind (s2n ".res") $ 
            pAnd (pEq (aeLength (aeVar ".res")) slengths)
                 (foldr pAnd pTrue p)

-- Only for debugging
ensureTysMatchDepBind :: [(AExpr, Ty)] -> DepBind () -> Check ()
ensureTysMatchDepBind [] (DPDone ()) = return ()
ensureTysMatchDepBind ((a, t) : args) (DPVar t1 sx xk) = do
    b <- isSubtype (tRefined t ".res" $ pEq (aeVar ".res") a) t1
    if b then do
         (x, k) <- unbind xk
         ensureTysMatchDepBind args $ subst x a k
    else do
        t' <- normalizeTy t
        t1' <- normalizeTy t1
        typeError ("Argument " ++ show (owlpretty a) ++ " does not match type " ++ sx ++ ": " ++ show (owlpretty t1') ++ "\nGot type " ++ show (owlpretty t'))

-- returns Nothing if input tys don't match; returns the output tys if they all
-- do match
tysMatchStructDef :: ResolvedPath -> TyVar -> [(AExpr, Ty)] -> [FuncParam] -> Bind [IdxVar] (DepBind ()) -> Check (Maybe [Ty])
tysMatchStructDef pth sname args ps b = do
    (is, dp) <- unbind b
    idxs <- getStructParams ps
    assert (show $ owlpretty "Wrong index arity for struct" <+> owlpretty pth <> owlpretty "." <> owlpretty sname ) $ length idxs == length is
    go args $ substs (zip is idxs) dp
        where
            go [] (DPDone ()) = return $ Just []
            go ((a, t):args) (DPVar t1 sx xk) = do
                b1 <- isSubtype t t1 
                checkTyPubLenOrGhost t
                case b1 of
                  False -> return Nothing
                  True -> do
                      (x, k) <- unbind xk
                      res <- go args $ subst x a k
                      case res of
                        Nothing -> return Nothing
                        Just ts -> return $ Just (t1 : ts)
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
                res <- tysMatchStructDef pth tv xs ps idf 
                case res of
                  Nothing -> trivialTypeOf (map snd xs)
                  Just outTs -> mkStructType pth tv xs outTs ps idf
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

aelem :: Alpha a => a -> [a] -> Bool
aelem x ys = any (aeq x) ys

tryResolvePropFromPathCondition :: Prop -> Check (Maybe Bool)
tryResolvePropFromPathCondition p = do
    pc <- view pathCondition
    if p `aelem` pc then return (Just True) else
        if (pNot p) `aelem` pc then return (Just False) else
        case p^.val of
          PEq a1 a2 -> do
              if (mkSpanned $ PEq a2 a1) `aelem` pc then return (Just True) else 
                  if (pNot $ mkSpanned $ PEq a2 a1) `aelem` pc then return (Just False) else 
                      return Nothing
          PEqIdx i1 i2 -> do 
              if (mkSpanned $ PEqIdx i2 i1) `aelem` pc then return (Just True) else 
                  if (pNot $ mkSpanned $ PEqIdx i2 i1) `aelem` pc then return (Just False) else 
                      return Nothing
          _ -> return Nothing


normalizeProp :: Prop -> Check Prop
normalizeProp = withMemoize (memoNormalizeProp) $ \p -> do
    ob <- tryResolvePropFromPathCondition p
    case ob of
      Just True -> return $ mkSpanned PTrue
      Just False -> return $ mkSpanned PFalse
      Nothing -> do
          p' <- go p
          if p' `aeq` p then return p' else normalizeProp p'
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
                     PNot (Spanned _ (PAnd p1 p2)) -> do
                         np1' <- normalizeProp $ pNot p1
                         np2' <- normalizeProp $ pNot p2
                         return $ pOr np1' np2'
                     PNot p1 -> do
                         p' <- normalizeProp p1
                         return $ Spanned (p^.spanOf) $ PNot p'
                     PQuantBV q sx xp -> do
                         (x, p') <- unbind xp
                         case p'^.val of
                           -- forall distributes over /\ (exists does not)
                           PAnd p1' p2' | Forall <- q -> normalizeProp $ Spanned (p^.spanOf) $ 
                                            PAnd 
                                                (mkSpanned $ PQuantBV q sx $ bind x p1') 
                                                (mkSpanned $ PQuantBV q sx $ bind x p2') 
                           _ -> do 
                             p2' <- withVars [(x, (ignore $ show x, Nothing, tGhost))] $ normalizeProp p'
                             return $ if x `elem` toListOf fv p2' then (Spanned (p^.spanOf) $ PQuantBV q sx (bind x p2')) else p2'
                     PQuantIdx q sx xp -> do
                         (x, p') <- unbind xp
                         case p'^.val of
                           -- forall distributes over /\ (exists does not)
                           PAnd p1' p2' | Forall <- q -> normalizeProp $ Spanned (p^.spanOf) $ 
                                            PAnd 
                                                (mkSpanned $ PQuantIdx q sx $ bind x p1') 
                                                (mkSpanned $ PQuantIdx q sx $ bind x p2') 
                           _ -> do 
                             p2' <- withIndices [(x, (ignore $ show x, IdxGhost))] $ normalizeProp p'
                             return $ if x `elem` toListOf fv p2' then (Spanned (p^.spanOf) $ PQuantIdx q sx (bind x p2')) else p2'
                     PFlow a b -> do
                         a' <- normLabel a
                         b' <- normLabel b
                         case (a'^.val, b'^.val) of
                           (LZero, _) -> return pTrue
                           _ | a' `aeq` b' -> return pTrue 
                           _ -> return (Spanned (p^.spanOf) $ PFlow a' b')
                     PHappened s ps as -> do
                         as' <- mapM (\a -> resolveANF a >>= normalizeAExpr) as
                         return $ Spanned (p^.spanOf) $ PHappened s ps as'
                     PApp s ps as -> do 
                         as' <- mapM (\a -> resolveANF a >>= normalizeAExpr) as
                         return $ Spanned (p^.spanOf) $ PApp s ps as'
                     PAADOf ne a -> do
                         ne' <- normalizeNameExp ne
                         a' <- resolveANF a >>= normalizeAExpr
                         return $ Spanned (p^.spanOf) $ PAADOf ne' a'               
                     PHonestPKEnc ne a -> do
                         ne' <- normalizeNameExp ne
                         a' <- resolveANF a >>= normalizeAExpr
                         return $ Spanned (p^.spanOf) $ PHonestPKEnc ne' a'
                     PHonestKEMEncaps ne a -> do
                         ne' <- normalizeNameExp ne
                         a' <- resolveANF a >>= normalizeAExpr
                         return $ Spanned (p^.spanOf) $ PHonestKEMEncaps ne' a'
                     _ -> return p


-- Normalize a type expression. Only nontrivial computations are to normalize a
-- nested refinement, and to normalize a case whether a name n is honest.


normalizeTy :: Ty -> Check Ty
normalizeTy = withMemoize (memoNormalizeTy) $ \t0 -> 
     withSpan (t0^.spanOf) $ local (set tcScope $ TcGhost False) $ do
         case t0^.val of
             TUnit -> return tUnit
             (TCase p' t1 t2) -> do
                 if t1 `aeq` t2 then normalizeTy t1 else do
                     p <- normalizeProp p'
                     case p^.val of
                       PTrue -> normalizeTy t1
                       PFalse -> normalizeTy t2
                       _ -> do
                           t1' <- pushPathCondition p $ do
                               normalizeTy t1
                           t2' <- pushPathCondition (pNot p) $ do
                               normalizeTy t2
                           return $ Spanned (t0^.spanOf) $ TCase p t1' t2'
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
             (TKEM_PK n) -> do
                 n' <- normalizeNameExp n
                 return $ Spanned (t0^.spanOf) $ TKEM_PK n'
             (TSS n m) -> do
                 n' <- normalizeNameExp n
                 m' <- normalizeNameExp m
                 b1 <- decideProp $ pFlow (nameLbl n') advLbl
                 let dhCombine x y = mkSpanned $ AEApp (topLevelPath "dh_combine") [] [x, y]
                 let dhpk x = mkSpanned $ AEApp (topLevelPath "dhpk") [] [x]
                 let corr_t = Spanned (t0^.spanOf) $ TRefined (tData advLbl advLbl) ".res" $
                         bind (s2n ".res") $
                             pEq (aeVar ".res") (dhCombine (dhpk (aeGet n')) (aeGet m'))
                 case b1 of
                   Just True -> return corr_t
                   _ -> do
                       b2 <- decideProp $ pFlow (nameLbl m') advLbl
                       case b2 of
                         Just True -> return corr_t
                         _ -> return $ Spanned (t0^.spanOf) $ TSS n' m'
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
             (TExistsIdx s xt) -> do
                 (x, t) <- unbind xt
                 t' <- withIndices [(x, (ignore s, IdxGhost))] $ normalizeTy t
                 return $ Spanned (t0^.spanOf) $ TExistsIdx s $ bind x t'
             TAdmit -> return t0
             THexConst a -> return t0

normalizeLabel :: Label -> Check Label
normalizeLabel l = do                
    normLabel l



-- Subtype checking, assuming the types are normalized


tUnitSimpl = 
    (tRefined (tData zeroLbl zeroLbl) "_x" $ (pEq (aeVar "_x") (aeApp (topLevelPath $ "unit") [] [])))

tDataWithLengthSimpl :: Label -> AExpr -> Check (Maybe Ty)
tDataWithLengthSimpl l a = do
    t <- inferAExpr a
    llen <- coveringLabel t
    llenPub <- tryFlowsTo llen advLbl
    case llenPub of
      Just True -> return $ Just $ tRefined (tData l advLbl) "_x" $ pEq (aeLength (aeVar "_x")) a
      _ -> return Nothing

mkRefineds :: Ty -> [(String, Bind DataVar Prop)] -> Ty
mkRefineds t [] = t
mkRefineds t ((s,p):ps) = mkSpanned $ TRefined (mkRefineds t ps) s p

checkSubRefinement t1 r1 t2 r2 = snd <$> (SMT.smtTypingQuery "" $ SMT.subTypeCheck (mkRefineds t1 r1) (mkRefineds t2 r2))

isSubtype' :: Ty -> [(String, Bind DataVar Prop)] -> Ty -> [(String, Bind DataVar Prop)] -> Check Bool
isSubtype' t1 r1 t2 r2 = local (set tcScope (TcGhost False)) $ do
    res <- withPushLog $ do
      structural <-
          case (t1^.val, t2^.val) of
            (t1', t2') | t1' `aeq` t2' -> return True
            (_, TGhost) -> return True
            (TAdmit, _) -> return True
            (TCase p t1' t2', _) -> do
                p' <- normalizeProp p
                (fn, r) <- SMT.symDecideProp p'
                case r of
                  Just b -> do
                      isSubtype' (if b then t1' else t2') r1 t2 r2
                  Nothing -> byCasesProp p' $ \b -> isSubtype' (if b then t1' else t2') r1 t2 r2
            (_, TCase p t1' t2') -> do
                p' <- normalizeProp p
                (fn, r) <- SMT.symDecideProp p'
                case r of
                  Just b -> do
                      isSubtype' t1 r1 (if b then t1' else t2') r2
                  Nothing -> byCasesProp p' $ \b -> isSubtype' t1 r1 (if b then t1' else t2') r2
            (TOption t1, TOption t2) -> isSubtype' t1 r1 t2 r2
            (_, TRefined t s p) -> isSubtype' t1 r1 t ((s,p):r2)
            (TRefined t s p, _) -> isSubtype' t ((s,p):r1) t2 r2
            (TExistsIdx s1 xt1, TExistsIdx s2 xt2) -> do
                (xi, t1) <- unbind xt1
                (xi', t2) <- unbind xt2
                withIndices [(xi, (ignore s1, IdxGhost))] $ 
                    isSubtype' t1 r1 (subst xi' (mkIVar xi) t2) r2
            (_, TUnit) -> isSubtype' t1 r1 tUnitSimpl r2
            (TUnit,  _) -> isSubtype' tUnitSimpl r1 t2 r2
            (TBool l1, TBool l2) -> do
                ob <- tryFlowsTo l1 l2
                case ob of
                  Nothing -> return False
                  Just b -> return b
            _ | isSingleton t2 -> return True
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
            (TSS n m, TSS m' n') | (n `aeq` n') && (m `aeq` m') -> return True
            (TDataWithLength l a, _) -> do
                ot1' <- tDataWithLengthSimpl l a
                case ot1' of
                  Nothing -> return False
                  Just t1' -> isSubtype' t1' r1 t2 r2
            (_, TDataWithLength l a) -> do
                ot2' <- tDataWithLengthSimpl l a
                case ot2' of
                  Nothing -> return False
                  Just t2' -> isSubtype' t1 r1 t2' r2
            (t, TData l1 l2 _) -> do
              l2' <- tyLenLbl t1
              b1 <- tyFlowsTo t1 l1 
              ob2 <- tryFlowsTo l2' l2
              case ob2 of
                Nothing -> return False
                Just b2 -> return $ b1 && b2
            _ -> do
                return False
      -- If we can't prove that `t1` is a subtype of `t2`, we check for an inconsistent context using SMT.
      -- This query appears to be very expensive, so we only do it if the subtyping check fails.
      if structural then return True else do
          x <- freshVar
          withVars [(s2n x, (ignore $ show x, Nothing, t1))] $ do
             (_, b) <- SMT.smtTypingQuery "false_elim" $ SMT.symAssert $ mkSpanned PFalse
             return b
    let t2Leaf = isSubtypeLeaf t2 
    if res then if t2Leaf then checkSubRefinement t1 r1 t2 r2 else return True else return False

isSubtypeLeaf t = 
    case t^.val of
      TData _ _ _ -> True
      TGhost -> True
      TConst _ _ -> True
      TBool _ -> True
      TUnit -> True
      TName _ -> True
      TVK _ -> True
      TDH_PK _ -> True
      TEnc_PK _ -> True
      TKEM_PK _ -> True
      TSS _ _ -> True
      TAdmit -> True
      THexConst _ -> True
      _ -> False 

isSingleton :: Ty -> Bool
isSingleton t = 
    case t^.val of
      TName _ -> True
      TVK _ -> True
      TDH_PK _ -> True
      TEnc_PK _ -> True
      TKEM_PK _ -> True
      TSS _ _ -> True
      THexConst _ -> True
      _ -> False

tyFlowsTo :: Ty -> Label -> Check Bool
tyFlowsTo t0 l = do
    t <- normalizeTy t0
    tyFlowsTo' (t, l)

tyFlowsTo' = withMemoize (memoTyFlowsTo') $ \(t, l) -> 
    case t^.val of
      TRefined t0 s xp -> do
          x <- freshVar
          withVars [(s2n x, (ignore $ show x, Nothing, t))] $
              tyFlowsTo t0 l
      TSS n m -> do
          ob1 <- tryFlowsTo (joinLbl (nameLbl n) advLbl) l
          ob2 <- tryFlowsTo (joinLbl (nameLbl m) advLbl) l
          return $ (ob1 == Just True) || (ob2 == Just True)
      _ -> do
          l1 <- coveringLabel t
          ob <- tryFlowsTo l1 l
          case ob of
            Nothing -> return False
            Just b -> return b

-- We check t1 <: t2  by first normalizing both
isSubtype :: Ty -> Ty -> Check Bool
isSubtype t1 t2 = go (t1, t2)
    where
        go = withMemoize (memoisSubtype') $ \(t1, t2) -> do 
            t1' <- normalizeTy t1
            t2' <- normalizeTy t2
            isSubtype' t1' [] t2' []



assertSubtype :: Ty -> Ty -> Check ()
assertSubtype t1 t2 = laxAssertion $ do
    tyc <- view tyContext
    b <- isSubtype t1 t2
    t1' <- normalizeTy t1
    t2' <- normalizeTy t2
    assert (show $ ErrCannotProveSubtype t1' t2') b


coveringLabel :: Ty -> Check Label
coveringLabel t = local (set tcScope $ TcGhost False) $ do
    coveringLabel' t


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
    -- The name is in scope in its own name type (recursive names)
    pth <- curModName
    local (over (curMod . nameDefs) $ insert n (bind (is1, is2) (BaseDef (nt, nls)))) $ 
        local (set curRecName $ Just (PDot pth n, is1)) $ 
            withIndices (map (\i -> (i, (ignore $ show i, IdxSession))) is1 ++ map (\i -> (i, (ignore $ show i, IdxPId))) is2) $ do
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
    withIndices (map (\i -> (i, (ignore $ show i, IdxSession))) is1 ++ map (\i -> (i, (ignore $ show i, IdxPId))) is2) $ do
        (xs, ne) <- unbind bne
        withVars (map (\x -> (x, (ignore $ show x, Nothing, tGhost))) xs) $ do
            _ <- getNameInfo ne
            return ()
    local (over (curMod . nameDefs) $ insert n (bind (is1, is2) (AbbrevNameDef bne))) $ k


sumOfLengths :: [(AExpr, Ty)] -> Check AExpr
sumOfLengths [] = return $ aeApp (topLevelPath $ "zero") [] []
sumOfLengths ((x, t):xs) = do
    ng <- tyNonGhost t
    xslen <- sumOfLengths xs
    case ng of
      True -> return $ aeApp (topLevelPath $ "plus") [] [aeLength x, xslen]
      False -> return $ xslen

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
    res <- withVars [(x, (ignore s, Nothing, t))] $ withDepBind d $ \args v -> k ((x, s, t):args) v
    return $ DPVar t s (bind x res)
                                          
unsafeMapDepBind :: Alpha a => DepBind a -> (a -> b) -> b
unsafeMapDepBind (DPDone x) k = k x
unsafeMapDepBind (DPVar _ _ xd) k = 
    let (x, d) = unsafeUnbind xd in
    unsafeMapDepBind d k

checkTyPubLenOrGhost :: Ty -> Check ()
checkTyPubLenOrGhost t = do
    case (stripRefinements t)^.val of
      TGhost -> return ()
      TConst s@(PRes (PDot pth tv)) ps -> do
          td <- getTyDef s
          case td of
            StructDef ib -> do
                (is, xs) <- unbind ib
                _ <- withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) is) $ do
                    withDepBind xs $ \args _ -> do 
                        forM_ args $ \(_, _, t) -> checkTyPubLenOrGhost t
                return ()
            EnumDef bs -> do
                bdy <- extractEnum ps (show s) bs
                forM_ bdy $ \(s, ot) -> 
                    case ot of
                      Nothing -> return ()
                      Just t0 -> 
                          checkTyPubLenOrGhost t0
            _ -> do
                  llbl <- tyLenLbl t
                  flowCheck llbl advLbl
      _ -> do
          llbl <- tyLenLbl t
          flowCheck llbl advLbl

                

                  
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
          withIndices (map (\i -> (i, (ignore $ show i, IdxSession))) is1 ++ map (\i -> (i, (ignore $ show i, IdxPId))) is2) $ do
              normLocality loc
          local (over (curMod . ctrEnv) $ insert n (bind (is1, is2) loc)) $ cont
      DeclSMTOption s1 s2 -> do
        local (over z3Options $ M.insert s1 s2) $ cont
      DeclFun s bnd -> do
          ufs <- view $ curMod . userFuncs
          assert ("Duplicate function: " ++ show s) $ not $ member s ufs
          (((is, ps), xs), a) <- unbind bnd
          withIndices (map (\i -> (i, (ignore $ show i, IdxSession))) is ++ map (\i -> (i, (ignore $ show i, IdxPId))) ps) $ do
              withVars (map (\x -> (x, (ignore $ show x, Nothing, tGhost))) xs) $ do
                  _ <- inferAExpr a
                  return ()
          local (over (curMod . userFuncs) $ insert s (FunDef bnd)) $ cont
      DeclPredicate s bnd -> do 
        preds <- view $ curMod . predicates
        assert ("Duplicate predicate: " ++ show s) $ not $ member s preds
        ((is, xs), p) <- unbind bnd
        local (set tcScope $ TcGhost False) $ do
            withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) is) $ do
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
          withIndices (map (\i -> (i, (ignore $ show i, IdxSession))) is1 ++ map (\i -> (i, (ignore $ show i, IdxPId))) is2) $ do
              normLocality l
          let df = DefHeader isl 
          addDef n df $ cont
      DeclDef n o1 -> do
          ((is1, is2), (l, db)) <- unbind o1
          dspec <- withIndices (map (\i -> (i, (ignore $ show i, IdxSession))) is1 ++ map (\i -> (i, (ignore $ show i, IdxPId))) is2) $ do
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
                              local (set tcScope $ TcDef l) $ local (set curDef $ Just n) $ 
                                  withVars [(s2n x, (ignore x, Nothing, mkSpanned $ TRefined tUnit ".req" (bind (s2n ".req") (pAnd preReq happenedProp))))] $ do
                                  _ <- withPushLog $ checkExpr (Just tyAnn) bdy''
                                  t1 <- liftIO $ getCurrentTime
                                  logTypecheck $ owlpretty $ "Finished checking " ++ n ++ " in " ++ show (diffUTCTime t1 t0)
                          return $ (preReq, tyAnn, Just bdy')
          let is_abs = ignore $ unsafeMapDepBind dspec $ \(_, _, o) -> not $ isJust o
          let df = Def $ bind (is1, is2) $ DefSpec is_abs l dspec
          addDef n df $ cont
      (DeclCorr ils) -> do
          ensureNoConcreteDefs
          ((is, xs), (l1, l2)) <- unbind ils
          withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) is) $ do
            withVars (map (\x -> (x, (ignore $ show x, Nothing, tGhost))) xs) $ do
              checkLabel l1
              checkLabel l2
          let cc = bind (is, xs) $ CorrImpl l1 l2
          local (over (curMod . advCorrConstraints) $ \xs -> cc : xs ) $ cont
      (DeclCorrGroup ils) -> do
          ensureNoConcreteDefs
          ((is, xs), ls) <- unbind ils
          withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) is) $ do
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
          snames_ <- withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) is) $ do
              withDepBind xs $ \args _ -> do 
                  snames <- forM args $ \(x, s, t) -> do 
                      checkTy t
                      assert (show $ owlpretty s <+> owlpretty "already defined") $ not $ member s dfs
                      checkTyPubLenOrGhost t
                      return s
                  return snames
          let snames = unsafeMapDepBind snames_ id 
          ufuncs <- view $ curMod . userFuncs
          let projs = map (\s -> (s, StructProjector n s)) snames 
          forM_ snames $ \sname -> 
              assert (show $ owlpretty sname <+> owlpretty "already defined") $ not $ member sname ufuncs
          local (over (curMod . userFuncs) $ insert n (StructConstructor n)) $ 
              local (over (curMod . userFuncs) $ mappend projs) $ 
                  addTyDef n (StructDef ixs) $ 
                      cont
      (DeclEnum n b) -> do
        (is, bdy) <- unbind b
        withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) is) $ do
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
          (((is, ps), xs), nt) <- unbind bnt
          withIndices (map (\i -> (i, (ignore $ show i, IdxSession))) is ++ map (\i -> (i, (ignore $ show i, IdxPId))) ps) $ do 
                withVars (map (\x -> (x, (ignore $ show x, Nothing, tGhost))) xs) $ do
                    checkNameType nt
          local (over (curMod . nameTypeDefs) $ insert s bnt) $ cont
      DeclKDFScope s ds -> checkKDFScope s ds cont
      DeclKDFRule l _ -> typeError $ "KDF rule '" ++ l ++ "' must be declared inside a kdf_scope"
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
      AELenConst _ -> return ()
      AEInt _ -> return ()

nameTypeUniform :: NameType -> Check ()
nameTypeUniform nt =  
    case nt^.val of
      NT_Nonce _ -> return ()
      NT_StAEAD _ _ _ _ -> return ()
      NT_Enc _ -> return ()
      NT_App p ps as -> resolveNameTypeApp p ps as >>= nameTypeUniform
      NT_MAC _ -> return ()
      NT_KDF -> return ()
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
                                        

checkNoTopLbl :: Bool -> Label -> Check ()
checkNoTopLbl allowGhost l = 
    case l^.val of
      LTop -> typeError $ "Top label not allowed here"
      LJoin l1 l2 -> do
          checkNoTopLbl allowGhost l1
          checkNoTopLbl allowGhost l2
      LRangeIdx il -> do
          (i, l) <- unbind il
          withIndices [(i, (ignore $ show i, IdxGhost))] $ checkNoTopLbl allowGhost l
      LRangeVar il -> do
          (x, l) <- unbind il
          checkNoTopLbl allowGhost l
      LGhost -> if allowGhost then return () else typeError $ "Ghost label not allowed here"
      _ -> return ()


checkNoTopTy :: Bool -> Ty -> Check ()
checkNoTopTy allowGhost t = 
    case t^.val of
      TData l1 l2 _ -> do
          checkNoTopLbl allowGhost l1
          checkNoTopLbl allowGhost l2
      TDataWithLength l _ -> checkNoTopLbl allowGhost l
      TRefined t _ _ -> checkNoTopTy allowGhost t
      TOption t -> checkNoTopTy allowGhost t
      TCase _ t1 t2 -> do
          checkNoTopTy allowGhost t1
          checkNoTopTy allowGhost t2
      TBool l -> checkNoTopLbl allowGhost l
      TGhost -> if allowGhost then return () else typeError $ "Ghost type not allowed here"
      TAdmit -> typeError $ "Admit type not allowed here"
      TExistsIdx s it -> do
          (i, t) <- unbind it
          withIndices [(i, (ignore s, IdxGhost))] $ checkNoTopTy allowGhost t
      TConst s ps -> do
          td <- getTyDef s
          forM_ ps checkParam
          forM_ ps $ \p -> 
              case p of
                ParamLbl l -> checkNoTopLbl allowGhost l
                ParamTy t -> checkNoTopTy allowGhost t
                _ -> return ()
          case td of
            TyAbstract -> return ()
            TyAbbrev t1 -> checkNoTopTy allowGhost t1
            StructDef ib -> do
                (is, xs) <- unbind ib
                _ <- withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) is) $ do
                    withDepBind xs $ \args _ -> do 
                        forM_ args $ \(_, _, t) -> checkNoTopTy True t
                return ()
            EnumDef b -> do
                ed <- extractEnum ps (show s) b
                forM_ ed $ \(_, ot) -> traverse (checkNoTopTy allowGhost) ot
      _ -> return ()      
          



checkNameType :: NameType -> Check ()
checkNameType nt = withSpan (nt^.spanOf) $ 
    case nt^.val of
      NT_KEM nt -> do
          checkNameType nt
          nameTypeUniform nt
      NT_DH -> return ()
      NT_Sig t -> do
          checkTy t
          checkNoTopTy False t
      NT_Nonce l -> do
          assert ("Unknown length constant: " ++ l) $ l `elem` lengthConstants 
          return ()
      NT_KDF -> return ()
      NT_Enc t -> do
        checkTy t
        checkNoTopTy False t
        checkTyPubLen t
      NT_App p ps as -> do
          resolveNameTypeApp p ps as >>= checkNameType
      NT_StAEAD t xsaad p ypat -> do
          checkTy t
          checkNoTopTy False t
          checkTyPubLen t
          ((x, slf), aad) <- unbind xsaad
          withVars [(x, (ignore $ show x, Nothing, tGhost)), (slf, (ignore $ show slf, Nothing, tGhost))] $ checkProp aad
          (y, pat) <- unbind ypat
          (y', _) <- freshen y
          let pat' = subst y (aeVar' y') pat
          let ghostNonceTy = tRefined tGhost ".res" $ pEq (aeLength (aeVar ".res")) (aeLenConst "counter")
          (_, pat_inj) <- withVars [(y, (ignore $ show y, Nothing, ghostNonceTy)), (y', (ignore $ show y', Nothing, ghostNonceTy))] $  local (set tcScope $ TcGhost False) $ do
              _ <- inferAExpr pat
              SMT.smtTypingQuery "pat_injectivity" $ SMT.symAssert $
                  pImpl (pEq pat pat') (pEq (aeVar' y) (aeVar' y'))
          assert ("Pattern injectivity failed") $ pat_inj
          checkCounter p
      NT_PKE t -> do
          checkTy t
          checkNoTopTy False t
          checkTyPubLen t
      NT_MAC t -> do
          checkTy t
          checkNoTopTy False t



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
    local (set tcScope $ TcGhost False) $ do
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
          (TExistsIdx s it) -> do
              (i, t) <- unbind it
              withIndices [(i, (ignore s, IdxGhost))] $ checkTy t
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
          (TKEM_PK n) -> do
              nt <- getNameType n
              case nt^.val of
                NT_KEM _ -> return ()
                _ -> typeError $ show $ ErrWrongNameType n "PKE" nt
          (TSS n m) -> do
              nt <- getNameType n
              nt' <- getNameType m
              case (nt^.val, nt'^.val) of
                (NT_DH, NT_DH) -> return ()
                (NT_DH, _) -> typeError $ show $ ErrWrongNameType n "DH" nt
                (_, NT_DH) -> typeError $ show $ ErrWrongNameType m "DH" nt
          (TCase p t1 t2) -> do
              local (set tcScope $ TcGhost False) $ checkProp p
              checkTy t1
              checkTy t2
          TAdmit -> return ()
          THexConst a -> 
              assert ("HexConst must have even length") $ length a `mod` 2 == 0


tyLenLbl :: Ty -> Check Label
tyLenLbl t =
    go False t
        where
            go inStruct t = 
                case t^.val of
                  TName _ -> return zeroLbl
                  TVK _ -> return zeroLbl
                  TDH_PK _ -> return zeroLbl
                  TEnc_PK _ -> return zeroLbl
                  TKEM_PK _ -> return zeroLbl
                  TSS _ _ -> return zeroLbl
                  TUnit -> return zeroLbl
                  TBool _ -> return zeroLbl
                  TGhost -> return $ if inStruct then zeroLbl else ghostLbl
                  TData _ l _ -> return l
                  TDataWithLength _ a -> do
                      t <- inferAExpr a
                      coveringLabel t
                  TRefined t' _ _ -> go inStruct t'
                  TOption t' -> do
                      l' <- go inStruct t'
                      return $ joinLbl advLbl l'
                  TConst s ps -> do
                      td <- getTyDef s
                      case td of
                        TyAbstract -> return advLbl
                        TyAbbrev t -> go inStruct t
                        StructDef b -> do
                            (is, xs) <- unbind b
                            idxs <- getStructParams ps
                            assert ("Wrong index arity for struct " ++ show (owlpretty s)) $ length is == length idxs
                            local (set tcScope $ TcGhost False) $ go2 $ substs (zip is idxs) xs
                                where
                                    go2 (DPDone _) = return zeroLbl
                                    go2 (DPVar t sx xk) = do
                                        l1 <- go True t
                                        (x, k) <- unbind xk
                                        l2_ <- withVars [(x, (ignore sx, Nothing, t))] $ go2 k
                                        let l2 = if x `elem` toListOf fv l2_ then (mkSpanned $ LRangeVar $ bind x l2_) else l2_
                                        return $ joinLbl l1 l2
                        EnumDef b -> do
                            bdy <- extractEnum ps (show s) b
                            ls <- forM bdy $ \(_, ot) ->
                                case ot of
                                  Just t' -> go inStruct t'
                                  Nothing -> return zeroLbl
                            return $ joinLbl advLbl (foldr joinLbl zeroLbl ls)
                  (TCase _ t1 t2) -> do
                      case t^.val of
                        TCase p _ _ -> do
                            l1 <- go inStruct t1
                            l2 <- go inStruct t2
                            return $ joinLbl l1 l2    
                        _ -> go inStruct t
                  (TExistsIdx s it) -> do
                      (i, t) <- unbind it
                      l <- withIndices [(i, (ignore s, IdxGhost))] $ go inStruct t
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
              withIndices [(i, (ignore $ show i, IdxGhost))] $ checkLabel l

checkProp :: Prop -> Check ()
checkProp p =
    local (set tcScope $ TcGhost False) $ withSpan  (p^.spanOf) $ do
        case p^.val of
          PHonestKEMEncaps ne a -> do
              nt <- local (set tcScope $ TcGhost False) $  getNameType ne
              case nt^.val of
                NT_KEM _ -> do
                    _ <- inferAExpr a
                    return ()
                _ -> typeError $ "Not a KEM key: " ++ show (owlpretty ne)
          PHonestPKEnc ne a -> do
              nt <- local (set tcScope $ TcGhost False) $  getNameType ne
              case nt^.val of
                NT_PKE _ -> do
                    _ <- inferAExpr a
                    return ()
                _ -> typeError $ "Not a PKE key: " ++ show (owlpretty ne)
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
              withIndices [(i, (ignore $ show i, IdxGhost))] $ checkProp p
          (PQuantBV _ _ xp) -> do
              (x, p) <- unbind xp
              withVars [(x, (ignore $ show x, Nothing, tGhost))] $ checkProp p 
          PApp s is xs -> do
              ts <- mapM inferAExpr xs
              p <- extractPredicate s is xs
              checkProp p
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
          (PEqIdx i1 i2) -> do
              checkIdx i1
              checkIdx i2



-- Handle trivial flows that can be checked without an SMT call.
trivialFlow :: Label -> Label -> Bool
trivialFlow l1 l2 =
    l1 `aeq` l2 ||
    (case l1^.val of
       LZero -> True
       LJoin a b -> trivialFlow a l2 && trivialFlow b l2
       _ -> False) ||
    (case l2^.val of
       LJoin a b -> trivialFlow l1 a || trivialFlow l1 b
       _ -> False)

flowsTo :: Label -> Label -> Check Bool
flowsTo l1' l2' = do
    l1 <- normalizeLabel l1'
    l2 <- normalizeLabel l2'
    if trivialFlow l1 l2 then return True else do
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
    if trivialFlow l1 l2 then return (Just True) else tryFlowsTo' (l1, l2)

tryFlowsTo' = withMemoizeDecided (memotryFlowsTo') $ \(l1, l2) -> do
    (fn, b) <- SMT.checkFlows l1 l2
    return b

decideProp :: Prop -> Check (Maybe Bool)
decideProp p = do
    p' <- normalizeProp p
    case p'^.val of
      PTrue -> return $ Just True
      PFalse -> return $ Just False
      _ -> flip (withMemoizeDecided memoDecideProp) p' $ \q -> do
        (fn, r) <- SMT.symDecideProp q
        return r

flowCheck :: Label -> Label -> Check ()
flowCheck l1 l2 = laxAssertion $ do
    b <- flowsTo l1 l2
    assert (show $ ErrFlowCheck l1 l2) b

-- Ensure l flows to LAdv





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
    case ot of 
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
              return (a, t)
          openArgs args $ \args' -> 
              getOutTy ot =<< checkCryptoOp (CLemma lem) args'
      ECrypt cop aes -> do
          args <- forM aes $ \a -> do
              t <- inferAExpr a
              withSpan (a^.spanOf) $ checkNoTopTy False t
              return (a, t)
          openArgs args $ \args' -> 
            getOutTy ot =<< checkCryptoOp cop args'
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
          t0' <- inferAExpr a
          openTy t0' $ \t' -> do 
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
      (EDebug (DebugCheckMatchesStruct args pth@(PRes (PDot p v)) ps)) -> do 
          argTys <- mapM inferAExpr args
          _ <- openArgs (zip args argTys) $ \args' -> do 
              md <- openModule p
              case lookup v (md^.tyDefs) of 
                Just (StructDef idf) -> do
                    sps <- getStructParams ps
                    (ixs, dp') <- unbind idf
                    assert ("Bad number of params for struct") $ length sps == length ixs
                    let dp = substs (zip ixs sps) dp'
                    ensureTysMatchDepBind args' dp
                    getOutTy ot $ tUnit
                _ -> typeError "Not a struct" 
          getOutTy ot $ tUnit
      (EDebug (DebugPrintPathCondition)) -> do
          pc <- view pathCondition
          logTypecheck $ owlpretty "Path condition: " <> list (map owlpretty pc)
          getOutTy ot $ tUnit
      (EDebug (DebugPrintModules)) -> do
          ms <- view openModules
          getOutTy ot $ tUnit
      (EDebug (DebugResolveANF a)) -> do
          logTypecheck $ owlpretty $ "resolving ANF on " ++ show (owlpretty a) ++ ":"
          b <- resolveANF a
          logTypecheck . owlpretty $ "Got " ++ show (owlpretty b)
          getOutTy ot $ tUnit
      (EDebug (DebugPrint s)) -> do
          logTypecheck $ owlpretty s
          getOutTy ot $ tUnit
      (EDebug (DebugPrintTyOf s a)) -> do
          t <- local (set tcScope $ TcGhost False) $ inferAExpr a
          a' <- resolveANF a
          t' <- normalizeTy t
          logTypecheck $ owlpretty "Type for " <> owlpretty s <> owlpretty ": " <> owlpretty t' 
          getOutTy ot $ tUnit
      (EDebug (DebugHasType s a t)) -> do
          checkTy t
          ta' <- local (set tcScope $ TcGhost False) $ inferAExpr a
          let ta = tRefined ta' ".res" $ pEq (aeVar ".res") a
          b <- isSubtype ta t
          logTypecheck $ owlpretty s <+> owlpretty "has type" <+> owlpretty t <> owlpretty ":" <+> owlpretty b 
          getOutTy ot $ tUnit
      (EDebug (DebugPrintTy t)) -> do
          t' <- normalizeTy t
          logTypecheck $ owlpretty t <+> owlpretty "normalizes to: " <> owlpretty t'
          getOutTy ot $ tUnit
      (EDebug (DebugDecideProp p)) -> do
          b <- decideProp p
          let pb = case b of
                     Just v -> owlpretty v
                     Nothing -> owlpretty "Inconclusive"
          logTypecheck $ owlpretty "Deciding " <> owlpretty p <> owlpretty ": " <> pb
          getOutTy ot $ tUnit
      (EDebug (DebugPrintTyContext anf)) -> do
          tC <- view tyContext
          let tC' = if anf then removeAnfVars tC else tC
          liftPutDoc $ owlprettyTyContext tC'
          getOutTy ot $ tUnit
      (EDebug (DebugPrintExpr e)) -> do
          logPutStrLn $ show $ owlpretty e
          getOutTy ot $ tUnit
      (EDebug (DebugPrintLabel l)) -> do
          logPutStrLn $ show $ owlpretty l
          getOutTy ot $ tUnit
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
          t1 <- (checkExpr tyAnn' e >>= normalizeTy)
          tc <- view tcScope
          (x, e') <- unbind xe'
          t2 <- withVars [(x, (ignore sx, anf, t1))] (checkExpr ot e')
          stripTy x t2 >>= normalizeTy
      ELetGhost a sx xk -> do
          t <- local (set tcScope $ TcGhost False) $ inferAExpr a
          t'' <- ghostifyTy a t
          (x, k) <- unbind xk
          t2 <- withVars [(x, (ignore sx, Just a, t''))] (checkExpr ot k)
          stripTy x t2
      (EChooseIdx s ip ik) -> do
          (ix, p) <- unbind ip
          withIndices [(ix, (ignore s, IdxGhost))] $ do
              checkProp p
          (_, b) <- SMT.symDecideProp $ mkSpanned $ PQuantIdx Exists (ignore s) ip
          (i, k) <- unbind ik
          getOutTy ot =<< case b of
            Just True -> do
                x <- freshVar
                let tx = tLemma (subst ix (mkIVar i) p) 
                to <- withIndices [(i, (ignore s, IdxGhost))] $ do
                    withVars [(s2n x, (ignore x, Nothing, tx))] $ checkExpr ot k
                if i `elem` getTyIdxVars to then
                    return (tExistsIdx s (bind i to))
                else return to
            _ -> do
                t' <- withIndices [(i, (ignore s, IdxGhost))] $ checkExpr ot k
                if i `elem` getTyIdxVars t' then
                    return (tExistsIdx s (bind i t'))
                else return t'
      (EChooseBV s ip ik) -> do
          (x, p) <- unbind ip
          withVars [(x, (ignore s, Nothing, tGhost))] $ do
              checkProp p
          (_, b) <- SMT.symDecideProp $ mkSpanned $ PQuantBV Exists (ignore s) ip
          (y, k) <- unbind ik
          getOutTy ot =<< case b of
            Just True -> do
                let tx = tRefined tGhost ".x" $ subst x (aeVar ".x") p
                to <- withVars [(x, (ignore s, Nothing, tx))] $
                    checkExpr ot $ subst y (aeVar' x) k
                if x `elem` toListOf fv to then 
                    stripTy x to
                else return to
            _ -> do
                to <- withVars [(y, (ignore s, Nothing, tGhost))] $ checkExpr ot k
                if y `elem` toListOf fv to then stripTy y to else return to
      (EUnpack a (si, sx) ixk) -> do
          t0 <- inferAExpr a
          -- i is fresh from unbind; binding the index under the source name si
          -- instead would let a nested unpack with the same name capture it.
          ((i, x), e) <- unbind ixk
          tyOfX <- openTy t0 $ \t -> do
              case (stripRefinements t)^.val of
                TExistsIdx _ jt' -> do
                    (j, t') <- unbind jt'
                    return $ tRefined (subst j (mkIVar i) t') ".res" (pEq (aeVar ".res") a)
                _ -> return t
          to <- withIndices [(i, (ignore si, IdxGhost))] $ do
              withVars [(x, (ignore $ sx, Nothing, tyOfX))] $ do
                  checkExpr ot e
          to' <- stripTy x to
          return $ if i `elem` getTyIdxVars to' then (tExistsIdx si (bind i to')) else to'
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
      EKEMEncaps a (s1, s2) xk -> do
          ta <- inferAExpr a                                                 
          b <- tyFlowsTo ta advLbl
          assert ("Cannot call KEM.Encaps on non-public expression") b
          t <- inferAExpr a
          keyType <- openTy t $ \t0 -> do
              case extractKEMPKFromType t0 of
                Nothing -> return $ tData advLbl advLbl
                Just k -> do
                    let n i = tRefined (tName $ mkSpanned $ KEMName k i) ".res" $ 
                                pImpl (pFlow (nameLbl k) advLbl)
                                      (pFlow (nameLbl $ mkSpanned $ KEMName k i) advLbl)
                    return $ tExistsIdx "i" $ bind (s2n ".i") $ n (mkIVar $ s2n ".i")
          let cipherType = tDataWithLength advLbl $ aeLenConst "kem_cipherlen"
          ((x1, x2), k) <- unbind xk
          t2 <- withVars [(x1, (ignore s1, Nothing, keyType)), (x2, (ignore s2, Nothing, cipherType))] $ checkExpr ot k
          stripTy x1 t2 >>= \t2' -> stripTy x2 t2 >>= normalizeTy
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
      EPackIdx j@(IVar _ _ xj) e1 -> do
          _ <- local (set tcScope $ TcGhost False) $ inferIdx j
          t1 <- checkExpr Nothing e1
          case ot of
            Just retT@(Spanned _ (TExistsIdx si it)) -> do
                (i, t) <- unbind it
                b <- isSubtype t1 (subst i j t)
                if b then return retT else (getOutTy ot $ mkSpanned $ TExistsIdx si $ bind xj t1)
            _ -> getOutTy ot $ mkSpanned $ TExistsIdx (show j) $ bind xj t1
      (EIf a e1 e2) -> do
          t <- inferAExpr a
          lt <- coveringLabel t
          flowCheck lt advLbl
          -- Carry forward refinements from t into the path condition
          pathRefinement <- case t ^. val of
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
          pathRefinement <- case t^.val of
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
          tres <- normalizeTy $ tRefined t ".res" (pEq (aeVar ".res") a)
          getOutTy ot tres 
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
               if b then do
                        pc <- view pathCondition
                        logTypecheck $ owlpretty "Reached contradiction! Path condition: " <> list (map owlpretty pc)
                        getOutTy ot tAdmit 
                    else checkExpr ot e
            False -> checkExpr ot e
      (ESetOption s1 s2 k) -> do
        local (over z3Options $ M.insert s1 s2) $ checkExpr ot k
      (EForallBV s xk) -> do
          (x, (oreq, k)) <- unbind xk
          t <- local (set tcScope $ TcGhost False) $ withVars [(x, (ignore s, Nothing, tGhost))] $ do
              case oreq of
                Just req -> do
                    checkProp req
                    xlem <- (\x -> "%" ++ x) <$> freshVar
                    withVars [(s2n xlem, (ignore xlem, Nothing, tLemma req))] $ 
                        checkExpr Nothing k
                Nothing -> checkExpr Nothing k
          case lemmaTyProp t of
            Just p' -> do
                let p2 = case oreq of
                           Nothing -> p'
                           Just req -> pImpl req p'
                getOutTy ot $ tLemma $ mkSpanned $ PQuantBV Forall (ignore s) $ bind x p2
            _ -> typeError $ "Unexpected return type of forall body: " ++ show (owlpretty t)
      (EForallIdx s ik) -> do
          (i, (oreq, k)) <- unbind ik
          tc <- view tcScope
          -- We allow crypto lemmas underneath forall_idx, because there are
          -- only polynomially many indices.
          -- If we already disallow crypto lemmas, though, continue to forbid
          -- them
          let tc' = case tc of
                      TcGhost False -> TcGhost False
                      _ -> TcGhost True
          t <- local (set tcScope $ tc') $ withIndices [(i, (ignore $ show i, IdxGhost))] $ do
              case oreq of
                Nothing -> checkExpr Nothing k
                Just req -> do
                    checkProp req
                    xlem <- (\x -> "%" ++ x) <$> freshVar
                    withVars [(s2n xlem, (ignore xlem, Nothing, tLemma req))] $ checkExpr Nothing k
          case lemmaTyProp t of
            Just p' -> do
                let p2 = case oreq of
                           Nothing -> p'
                           Just req -> pImpl req p'
                getOutTy ot $ tLemma $ mkSpanned $ PQuantIdx Forall (ignore s) $ bind i p2
            _ -> typeError $ "Unexpected return type of forall body: " ++ show (owlpretty t)
      EOpenTyOf a k -> do
          t <- inferAExpr a >>= normalizeTy
          openTy t $ \_ -> checkExpr ot k
      (ECorrCaseNameOf a op k) -> do
          t <- inferAExpr a
          case extractNameFromType t of
            Just n ->  checkExpr ot $ Spanned (e^.spanOf) $ EPCase (pFlow (nameLbl n) advLbl) op Nothing k
            Nothing -> checkExpr ot k
      (EPCase p op attr k) -> do
          _ <- local (set tcScope $ TcGhost False) $ checkProp p
          doCaseSplit <- case op of
                           Nothing -> return True
                           Just pcond -> do 
                               _ <- local (set tcScope $ TcGhost False) $ checkProp pcond
                               (_, b) <- SMT.smtTypingQuery "case split condition" $ SMT.symAssert pcond
                               return b 
          let (doFalse, doTrue) = case attr of
                                    Nothing -> (True, True)
                                    Just False -> (True, False)
                                    Just True -> (False, True)
          case doCaseSplit of 
            False -> checkExpr ot k
            True -> do 
              let pcase_line = fst $ begin $ unignore $ e^.spanOf
              x <- fresh $ s2n "%caseProp"
              let checkTrue = case doTrue of
                         True -> 
                             withVars [(x, (ignore $ "pcase_true (line " ++ show pcase_line ++ ")", Nothing, tLemma p))] $ pushPathCondition p $ do
                                  logTypecheck $ owlpretty "Case split: " <> owlpretty p
                                  withPushLog $ do 
                                      (_, b) <- SMT.smtTypingQuery "case split prune" $ SMT.symAssert $ mkSpanned PFalse
                                      if b then return Nothing else Just <$> checkExpr ot k
                         False -> return $ Just tAdmit
              let checkFalse = case doFalse of
                         True -> 
                             withVars [(x, (ignore $ "pcase_false (line " ++ show pcase_line ++ ")", Nothing, tLemma (pNot p)))] $ pushPathCondition (pNot p) $ do
                                  logTypecheck $ owlpretty "Case split: " <> owlpretty (pNot p)
                                  withPushLog $ do 
                                      (_, b) <- SMT.smtTypingQuery "case split prune" $ SMT.symAssert $ mkSpanned PFalse
                                      if b then return Nothing else Just <$> checkExpr ot k
                         False -> return $ Just tAdmit
              (otTrue, otFalse) <- parBoth checkTrue checkFalse
              -- A pruned branch is infeasible on this path, so the other
              -- branch's type alone is the type of the split. This keeps
              -- Admit out of the type of a let-bound split.
              tMerge <- case (otTrue, otFalse) of
                          (Nothing, Nothing) -> return tAdmit
                          (Nothing, Just tFalse) -> normalizeTy tFalse
                          (Just tTrue, Nothing) -> normalizeTy tTrue
                          (Just tTrue, Just tFalse) -> normalizeTy $ mkSpanned $ TCase p tTrue tFalse
              getOutTy ot tMerge
      EParse a t ok bk -> do
          retT <- case ot of
                    Just t -> return t
                    Nothing -> typeError $ "parse must have expected return type"
          t1 <- inferAExpr a
          checkTy t
          sinfo <- obtainStructInfoTopDown a t
          otherwiseCase <- case ok of
                             Nothing -> return False
                             Just k' -> do
                                 _ <- checkExpr (Just retT) k'
                                 return True
          bindingTys <- computeStructBindings t1 t sinfo otherwiseCase
          (b, k) <- unbind bk
          assert ("Wrong number of variables on parse statement") $ length b == length sinfo
          bindings <- forM (zip b bindingTys) $ \((x, s), t) -> return (x, (s, Nothing, t))
          withVars bindings $ checkExpr (Just retT) k
          normalizeTy retT
      (ECase e1 otk cases) -> do
          t <- checkExpr Nothing e1
          e1_a <- case e1^.val of
                    ERet a -> return a
                    _ -> typeError "Expected AExpr for case after ANF"
          t <- stripRefinements <$> normalizeTy t
          retT <- case ot of
                    Just t -> return t
                    Nothing -> typeError $ "case must have expected return type"
          ((enumPath, tcases), tEnum, hasOtherwise) <- case otk of
                      Just (tAnn, k) -> do
                          checkTy tAnn
                          _ <- checkExpr (Just retT) k
                          tc <- obtainTyCases tAnn ""
                          return (tc, tAnn, True)
                      Nothing -> do
                          tc <- obtainTyCases t ". Try adding an annotation to the case statement." 
                          return (tc, t, False)
          assert ("Duplicate case found in case statement") $ uniq $ map fst cases
          assert ("Case split inexhaustive") $ (S.fromList (map fst cases)) == (S.fromList (map fst tcases)) 
          let caseNameArities = S.fromList $ map (\(s, ot) -> (s, isJust ot)) tcases
          ensureTyCanBeCased t hasOtherwise
          forM_ cases $ \(c, cse) -> do 
              let (Just otcase) = lookup c tcases
              case (otcase, cse) of
                (Nothing, Left ek) -> do
                    x <- freshVar
                    _ <- withVars [(s2n x, (ignore $ show x, Nothing, tLemma $ pEq aeTrue $ aeApp (PRes $ PDot enumPath $ c ++ "?") [] [e1_a]))] $
                        checkExpr (Just retT) ek
                    return ()
                (Just t1, Right (xs, bnd)) -> do
                    (x, k) <- unbind bnd
                    xt <- normalizeTy =<< computeEnumDataType tEnum t t1 caseNameArities c
                    let xt_refined = tRefined xt "._" $ pEq aeTrue $ aeApp (PRes $ PDot enumPath $ c ++ "?") [] [e1_a]
                    _ <- withVars [(x, (xs, Nothing, xt_refined))] $ checkExpr (Just retT) k
                    return ()
                _ -> do
                    let ar1 = case otcase of
                                  Nothing -> 0
                                  Just _ -> 1
                    let ar2 = case cse of
                                  Left _ -> 0
                                  Right _ -> 1
                    typeError $ "Mismatch on branch case" ++ c ++ ": expected arity " ++ show ar1 ++ ", got " ++ show ar2
          normalizeTy retT
      _ -> error $ "Unhandled expr: " ++ show e

ensureTyCanBeCased :: Ty -> Bool -> Check ()
ensureTyCanBeCased t hasOtherwise = 
    when hasOtherwise $ do 
        analyzeTyByCases t $ \t0 -> do 
            otcs <- tryObtainTyCases t0 
            case otcs of
              Just _ -> return () -- t0 is a case-able enum or option
              Nothing -> do -- overapproximate
                l <- coveringLabel t0
                flowCheck l advLbl

computeStructBindings :: Ty -> Ty -> [(String, Ty)] -> Bool -> Check [Ty]
computeStructBindings targ tann sinfo hasOtherwise = 
    case (stripRefinements targ)^.val of
      TCase p t1 t2 -> casePropTyList p $ \b -> computeStructBindings (if b then t1 else t2) tann sinfo hasOtherwise
      _ -> do
          b <- isSubtype targ tann
          case b of
            True ->  return $ map snd sinfo
            False -> do
                assert ("Parse statement needs an otherwise case here") $ hasOtherwise
                l <- coveringLabel targ
                validatedTys <- getValidatedStructTys (show $ owlpretty tann) l sinfo
                return $ map snd validatedTys




computeEnumDataType :: Ty -> Ty -> Ty -> S.Set (String, Bool) -> String -> Check Ty
computeEnumDataType tEnum -- Type of overall enum
                    t -- Type of argument
                    t1 -- Type of parsed argument (worst case)
                    caseNameArities 
                    c = do -- Enum case name
    case (stripRefinements t)^.val of
      TCase p ta tb -> casePropTy p $ \b -> computeEnumDataType tEnum (if b then ta else tb) t1 caseNameArities c
      _ -> do
          otcs <- tryObtainTyCases t 
          case otcs of
            Just (_, tcs) -> do
                assert ("Casing on wrong enum") $ caseNameArities == S.fromList (map (\(x, ot) -> (x, isJust ot)) tcs) 
                case lookup c tcs of
                  Just (Just to) -> return to
                  _ -> typeError "unreachable"
            Nothing -> do
                ot <- getValidatedTy advLbl t1
                case ot of
                  Just to -> return to
                  Nothing -> return $ tData advLbl advLbl


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
                withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) is) $ do
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
        TUnit -> return $ Just tUnit
        TName ne -> do
            nameLen <- getLenConst ne
            return $ Just $ tDataWithLength albl nameLen
        TVK _ -> return $ Just $ tDataWithLength albl (aeLenConst "vk")
        TDH_PK _ -> return $ Just $ tDataWithLength albl (aeLenConst "group")
        TEnc_PK _ -> return $ Just $ tDataWithLength albl (aeLenConst "pke_pk")
        TKEM_PK _ -> return $ Just $ tDataWithLength albl (aeLenConst "kem_pk")
        TSS _ _ -> return $ Just $ tDataWithLength albl (aeLenConst "group")
        TAdmit -> typeError $ "Unparsable type: " ++ show (owlpretty t)
        TExistsIdx s ity -> do
            (i, ty) <- unbind ity
            withIndices [(i, (ignore s, IdxGhost))] $ getValidatedTy albl ty
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
                            NT_Nonce l -> return $ mkSpanned $ AELenConst l
                            NT_Enc _ -> return $ mkSpanned $ AELenConst "enckey"
                            NT_App p ps as -> resolveNameTypeApp p ps as >>= go
                            NT_StAEAD _ _ _ _ -> return $ mkSpanned $ AELenConst "enckey"
                            NT_MAC _ -> return $ mkSpanned $ AELenConst "mackey"
                            NT_DH -> return $ mkSpanned $ AELenConst "group"
                            NT_Sig _ -> return $ mkSpanned $ AELenConst "signature"
                            NT_PKE _ -> return $ mkSpanned $ AELenConst "pke_sk"
                            NT_KDF -> return $ mkSpanned $ AELenConst "kdfkey"
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
                  mkSpanned <$> enforcePublicArguments "Encryption ill typed, so all arguments must be public" [t1, t]
          _ -> typeError $ show $ ErrWrongNameType k "encryption key" nt
    _ -> do
        mkSpanned <$> enforcePublicArguments "Encryption ill typed, so all arguments must be public" [t1, t]

doADec t1 t args = do
    case extractNameFromType t1 of
      Just k -> do
          nt <-  local (set tcScope $ TcGhost False) $ getNameType k
          case nt^.val of
            NT_Enc t' -> do
                b <- tyFlowsTo t advLbl -- Public ciphertext
                casePropTy (pFlow (nameLbl k) advLbl) $ \b2 ->  -- b2 = k is corrupt
                    if ((not b2) && b) then do -- k secret and cipher public
                        -- Honest
                        return $ mkSpanned $ TOption t'
                    else if (b && b2) then do -- everything public
                        return $ mkSpanned $ TOption $ tDataAnn advLbl advLbl "Public adec"
                    else do
                        mkSpanned <$> enforcePublicArgumentsOption "Decryption ill typed, so all arguments must be public" [t1, t]
            _ -> typeError $ show $  ErrWrongNameType k "encryption key" nt
      _ -> do
          mkSpanned <$> enforcePublicArgumentsOption "Decryption ill typed, so all arguments must be public" [t1, t]

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

nameKindLength :: NameKind -> AExpr
nameKindLength nk =
    aeLenConst $ case nk of
                               NK_KDF -> "kdfkey"
                               NK_DH -> "dhkey"
                               NK_Enc -> "enckey"
                               NK_PKE -> "pkekey"
                               NK_Sig -> "sigkey"
                               NK_MAC -> "mackey"
                               NK_Nonce l -> l

crhInjLemma :: AExpr -> AExpr -> Check Prop
crhInjLemma x y = 
    case (x^.val, y^.val) of
      (AEApp (PRes (PDot PTop "crh")) [] [a], AEApp (PRes (PDot PTop "crh")) [] [b]) -> do
          let p1 = pImpl (pEq x y) (pEq a b)
          p2 <- crhInjLemma a b
          return $ pAnd p1 p2
      (AEApp (PRes (PDot PTop "concat")) [] [a, b], AEApp (PRes (PDot PTop "concat")) [] [c, d]) -> do
          p1 <- crhInjLemma a c
          p2 <- crhInjLemma b d
          return $ pAnd p1 p2
      _ -> return pTrue

-- kdf_inj_lemma(x, y): the kdf_collision_resistant_on_large_slices instance for two gkdf terms of the same
-- kind, and for the gkdf terms nested in their inputs. Like the axiom, it says
-- nothing about a slice that may be shorter than MinKDFSliceLen (kdfInjKinds).
kdfInjLemma :: AExpr -> AExpr -> Check Prop
kdfInjLemma x y =
    case (x^.val, y^.val) of
      (AEKDF a b c nks j, AEKDF a' b' c' nks' j')
        | j < length nks && j' < length nks' && (nks !! j == nks' !! j') && (nks !! j) `elem` kdfInjKinds -> do
          let p1 = pImpl (pEq x y) (pAnd (pAnd (pEq a a') (pEq b b')) (pEq c c'))
          p2 <- kdfInjLemma a a'
          p3 <- kdfInjLemma b b'
          return $ pAnd p1 $ pAnd p2 p3
      (AEApp (PRes (PDot PTop "concat")) [] [a, b], AEApp (PRes (PDot PTop "concat")) [] [c, d]) -> do
          p1 <- kdfInjLemma a c
          p2 <- kdfInjLemma b d
          return $ pAnd p1 p2
      _ -> return pTrue

patternPublicAndEquivalent :: Bind DataVar AExpr -> Bind DataVar AExpr -> Check (Bool, Bool)
patternPublicAndEquivalent pat1 pat2 = do
    (x, pat) <- unbind pat1
    (y, pat') <- unbind pat2
    let ctrTy = tRefined (tData advLbl advLbl) ".res" $ pEq (aeLength (aeVar ".res")) (aeLenConst "counter")
    withVars [(x, (ignore $ show x, Nothing, ctrTy))] $ do
        t <- inferAExpr pat
        b1 <- tyFlowsTo t advLbl
        if b1 then do
              (_, b2) <- SMT.smtTypingQuery "pattern equivalence check" $ SMT.symAssert $ pEq pat (subst y (aeVar' x) pat')
              return (True, b2)
        else return (False, False)



checkCryptoOp :: CryptOp -> [(AExpr, Ty)] -> Check Ty
checkCryptoOp cop args = pushRoutine ("checkCryptoOp(" ++ show (owlpretty cop) ++ ")") $ do
    tcs <- view tcScope
    case (tcs, cop) of
      -- secret_neq_lemma is allowed under forall x:bv; a bound bitstring has
      -- type Ghost, so it can never be the lemma's public argument
      (TcGhost _, CLemma LemmaSecretNeq) -> return ()
      (TcGhost b, CLemma _) -> assert ("Lemma " ++ show (owlpretty cop) ++ " cannot be called here") b
      (TcGhost _, _) -> typeError $ "Crypto op " ++ show (owlpretty cop) ++ " cannot be executed in ghost"
      _ -> return ()
    case cop of
      CLemma (LemmaKDFInj) -> local (set tcScope $ TcGhost False) $ do 
          assert ("kdf_inj_lemma takes two arguments") $ length args == 2
          let [(x, _), (y, _)] = args
          x' <- resolveANF x >>= normalizeAExpr
          y' <- resolveANF y >>= normalizeAExpr
          p <- kdfInjLemma x' y'
          return $ tLemma p 
      CLemma (LemmaCRH) -> local (set tcScope $ TcGhost False) $ do 
          assert ("crh_lemma takes two arguments") $ length args == 2
          let [(x, _), (y, _)] = args
          x' <- resolveANF x >>= normalizeAExpr
          y' <- resolveANF y >>= normalizeAExpr
          p <- crhInjLemma x' y'
          return $ tLemma p 
      CLemma (LemmaDisjNotEq) -> do
          assert ("disjoint_not_eq_lemma takes two arguments") $ length args == 2
          let [(x, _), (y, _)] = args
          x' <- normalizeAExpr =<< resolveANF x
          y' <- normalizeAExpr =<< resolveANF y
          proveDisjointContents x' y'
          return $ tRefined tUnit "._" $ pNot $ pEq x' y'
      CLemma (LemmaCrossDH n) -> crossDHLemma n args
      CLemma LemmaSecretNeq -> local (set tcScope $ TcGhost False) $ do
          assert ("secret_neq_lemma takes two arguments") $ length args == 2
          let [(x, _), (y, _)] = args
          tLemma <$> secretNeqLemma x y
      CLemma (LemmaDHExp s n) -> dhExpLemma s n args
      CLemma (LemmaKDFLabel n) -> do
          assert ("kdf_label_lemma takes no arguments") $ null args
          tLemma <$> kdfLabelLemma n
      CLemma (LemmaConstant)  -> do
          assert ("Wrong number of arguments to is_constant_lemma") $ length args == 1
          let [(x, _)] = args
          x' <- resolveANF x
          x'' <- normalizeAExpr x'
          let b = isConstant x''
          assert ("Argument is not a constant: " ++ show (owlpretty x'')) b
          return $ tRefined tUnit "._" $ mkSpanned $ PIsConstant x''
      CKDF hints nks j -> do
          assert ("KDF must take three arguments") $ length args == 3
          let [a, b, c] = args -- salt, ikm, info
          checkKDFCall hints nks j a b c
      CKEMDecaps -> do
          assert ("Wrong number of arguments to kem_decaps") $ length args == 2
          let [(_, t1), (x, t2)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> trivialTypeOf [t1, t2]
            Just k -> do
                nt <- local (set tcScope $ TcGhost False) $ getNameType k
                case nt^.val of
                  NT_KEM _ -> do
                      b2 <- tyFlowsTo t2 advLbl 
                      casePropTy (pFlow (nameLbl k) advLbl) $ \b1 -> 
                          if b2 && (not b1) then 
                              return $ mkSpanned $ TOption $ mkSpanned $ 
                                    TCase (mkSpanned $ PHonestKEMEncaps k x)
                                        (tExistsIdx "i" $ bind (s2n ".i") $ tName $ mkSpanned $ KEMName k (mkIVar $ s2n ".i"))
                                        (tDataAnn advLbl advLbl "adversarial kem encaps")
                          else if b2 && b1 then  
                            return $ mkSpanned $ TOption $ tDataAnn advLbl advLbl "corrupt kem_decaps"
                          else mkSpanned <$> trivialTypeOf [t1, t2]
                  _ -> mkSpanned <$> trivialTypeOfAnn "wrong name type for kem_decaps" [t1, t2]
      CAEnc -> do
          assert ("Wrong number of arguments to encryption") $ length args == 2
          let [(_, t1), (x, t)] = args
          doAEnc t1 x t args
      CADec -> do 
          assert ("Wrong number of arguments to decryption") $ length args == 2
          let [(_, t1), (_, t)] = args
          doADec t1 t args
      CEncStAEAD p iargs xpat -> do
          checkCounterIsLocal p iargs
          assert ("Wrong number of arguments to stateful AEAD encryption") $ length args == 3
          let [(_, t1), (x, t), (y, t2)] = args
          let withCorrectLength k = do
                      t <- k
                      return $ tRefined t ".res" $ pEq (aeLength (aeVar ".res")) 
                        (aeApp (topLevelPath $ "cipherlen") [] [aeLength x])
          withCorrectLength $ case extractNameFromType t1 of
            Nothing -> mkSpanned <$> enforcePublicArguments "Invalid key, so arguments must be public" (map snd args)
            Just k -> do
                nt <- local (set tcScope $ TcGhost False) $ getNameType k
                case nt^.val of
                  NT_StAEAD tm xaad p' ypat' -> do
                      pnorm <- normalizePath p
                      pnorm' <- normalizePath p'
                      assert ("Wrong counter for AEAD: expected " ++ show (owlpretty p') ++ " but got " ++ show (owlpretty p)) $ pnorm `aeq` pnorm'
                      b1 <- isSubtype t tm
                      ((xa, xslf), aadp) <- unbind xaad
                      b2 <- isSubtype t2 $ tRefined (tData advLbl advLbl) ".res" $
                          pImpl (pNot $ pFlow (nameLbl k) advLbl)
                                (subst xa (aeVar ".res") $ subst xslf (aeGet k) $  aadp)
                      (b3, b4) <- patternPublicAndEquivalent xpat ypat'
                      if b1 && b2 && b3 && b4 then return $ tData advLbl advLbl 
                                  else do
                                      let err_msg = case (b1, b2, b3, b4) of
                                                      (False, _, _, _) -> "Invalid message type"
                                                      (_, False, _, _) -> "Invalid AAD"
                                                      (_, _, False, _) -> "Nonce pattern not public"
                                                      (_, _, _, False) -> "Invalid nonce pattern"
                                      mkSpanned <$> enforcePublicArguments (err_msg ++ ", so arguments must be public") (map snd args)
                  _ -> mkSpanned <$> enforcePublicArguments "Name type invalid for key, so arguments must be public" (map snd args)
      CDecStAEAD -> do
          assert ("Wrong number of arguments to stateful AEAD decryption") $ length args == 4
          let [(_, t1), (x, t), (y, t2), (xnonce, tnonce)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> enforcePublicArgumentsOption "Decryption ill-typed, so arguments must be public" [t1, t, t2, tnonce]
            Just k -> do
                nt <- local (set tcScope $ TcGhost False) $ getNameType k
                case nt^.val of
                  NT_StAEAD tm xaad _ ypat -> do
                      b1 <- flowsTo (nameLbl k) advLbl
                      b2 <- tyFlowsTo tnonce advLbl
                      b3 <- tyFlowsTo t advLbl
                      b4 <- tyFlowsTo t2 advLbl
                      if (not b1) && b2 && b3 && b4 then do
                            ((x, xslf), aad) <- unbind xaad
                            return $ mkSpanned $ TOption $ tRefined tm ".res" $ subst x y $ subst xslf (aeGet k) $ aad
                      else  mkSpanned <$> enforcePublicArgumentsOption "Decryption ill-typed, so arguments must be public" [t1, t, t2, tnonce]
                  _ ->  mkSpanned <$> enforcePublicArgumentsOption "Decryption ill-typed, so arguments must be public" [t1, t, t2, tnonce]
      CPKDec -> do 
          assert ("Wrong number of arguments to pk decryption") $ length args == 2
          let [(_, t1), (xm, t)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> enforcePublicArgumentsOption "pk dec ill-typed, so arguments must be public" [t1, t]
            Just k -> do
              nt <- local (set tcScope $ TcGhost False) $  getNameType k
              case nt^.val of
                NT_PKE t' -> do
                    l <- coveringLabel t
                    b1 <- flowsTo l advLbl
                    casePropTy (pFlow (nameLbl k) advLbl) $ \b2 -> 
                        if b1 && (not b2) then do
                            return $ mkSpanned $ TOption $ mkSpanned $ 
                                TCase (mkSpanned $ PHonestPKEnc k xm)
                                      t'
                                      (tDataAnn advLbl advLbl "adversarial message")
                        else mkSpanned <$> enforcePublicArgumentsOption "pk dec ill-typed, so arguments must be public" [t1, t]
      CPKEnc -> do 
          assert ("Wrong number of arguments to pk encryption") $ length args == 2
          let [(_, t1), (x, t)] = args
          case extractEncPKFromType t1 of
            Nothing -> mkSpanned <$> enforcePublicArguments "pk enc ill-typed, so arguments must be public" [t1, t]
            Just k -> do
                nt <- local (set tcScope $ TcGhost False) $  getNameType k
                case nt^.val of
                  NT_PKE t' -> do
                      b <- isSubtype t t'
                      if (b) then
                          return $ mkSpanned $ TRefined (tData advLbl advLbl) ".res" $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (aeApp (topLevelPath $ "pk_cipherlen") [] [aeLength x])
                      else mkSpanned <$> enforcePublicArguments "pk enc ill-typed, so arguments must be public" [t1, t]
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
                  _ -> mkSpanned <$> enforcePublicArguments "mac ill-typed, so arguments must be public" [t1, t]
      CMacVrfy -> do
          assert ("Wrong number of arguments to mac_vrfy") $ length args == 3
          let [(xt1, t1), (m, mt), (xt, t)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> enforcePublicArgumentsOption "mac vrfy ill-typed, so arguments must be public" [t1, mt, t]
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
                      else mkSpanned <$> enforcePublicArgumentsOption "mac vrfy ill-typed, so arguments must be public" [t1, mt, t]
      CSign -> do
          assert ("Wrong number of arguments to sign") $ length args == 2
          let [(_, t1), (_, t)] = args
          case extractNameFromType t1 of
            Nothing -> mkSpanned <$> enforcePublicArguments "sign ill-typed, so arguments must be public" [t1, t]
            Just sk -> do
                nt <- local (set tcScope $ TcGhost False) $  getNameType sk
                case nt^.val of
                  NT_Sig t' -> do
                      assertSubtype t t'
                      l <- coveringLabel t'
                      return $ mkSpanned $ TRefined (tData l advLbl) ".res" $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (mkSpanned $ AELenConst "signature")
                  _ -> mkSpanned <$> enforcePublicArguments "sign ill-typed, so arguments must be public" [t1, t]
      CSigVrfy -> do
          assert ("Wrong number of arguments to vrfy") $ length args == 3
          let [(_, t1), (_, t2), (_, t3)] = args
          case extractVKFromType t1 of
            Nothing -> mkSpanned <$> enforcePublicArgumentsOption "sig vrfy ill-typed, so arguments must be public" [t1, t2, t3]
            Just k -> do 
                nt <-  local (set tcScope $ TcGhost False) $ getNameType k
                case nt^.val of
                  NT_Sig t' -> do
                      l <- coveringLabel t'
                      let l' = joinLbl l advLbl
                      b1 <- tyFlowsTo t2 l'
                      b2 <- tyFlowsTo t3 l'
                      casePropTy (pFlow (nameLbl k) advLbl) $ \b3 -> 
                          if (b1 && b2 && (not b3)) then return (mkSpanned $ TOption t')
                          else mkSpanned <$> enforcePublicArgumentsOption "sig vrfy ill-typed, so arguments must be public" [t1, t2, t3]
                  _ -> typeError $ show $ ErrWrongNameType k "sig" nt

aundup :: Alpha a => [a] -> [a]
aundup [] = []
aundup (x:xs) = if x `aelem` xs then aundup xs else x : aundup xs

-- The proposition of a lemma type: a refined unit, or a case split over such
-- (a lemma whose arguments have conditional types)
lemmaTyProp :: Ty -> Maybe Prop
lemmaTyProp t = 
    case t^.val of
      TRefined (Spanned _ TUnit) _ yp -> 
          let (y, p) = unsafeUnbind yp in
          Just $ subst y (aeApp (topLevelPath "unit") [] []) p
      TCase p t1 t2 -> do
          p1 <- lemmaTyProp t1
          p2 <- lemmaTyProp t2
          return $ pImpl p p1 `pAnd` pImpl (pNot p) p2
      _ -> Nothing

---- Entry point ----

typeCheckDecls :: Flags -> [Decl] -> IO (Either (Env SMT.SolverEnv) (Env SMT.SolverEnv))
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

normalizeTyContext :: Map DataVar (Ignore String, (Maybe AExpr), Ty) -> Check (Map DataVar (Ignore String, (Maybe AExpr), Ty))
normalizeTyContext ctxt =
    forM ctxt $ \(x, (s, a, t)) -> do
        t' <- normalizeTy t
        return (x, (s, a, t'))

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
    tyc <- case ite of
             True -> removeAnfVars <$> view tyContext
             False -> do
                f <- view $ envFlags . fLocalTypeError
                (if (not f) then local (set pathCondition []) else id) $ 
                    local (set inTypeError True) $ (removeAnfVars <$> view tyContext) >>= normalizeTyContext
    let rep = E.Err Nothing msg [(pos, E.This msg)] info
    let diag = E.addFile (E.addReport def rep) (fn) f  
    noColor <- view $ envFlags . fNoColor
    let putDoc' d = liftIO $ putDoc $ if noColor then unAnnotate d else d
    putDoc' $ owlpretty "Type context" <> line <> pretty "===================" <> line <> owlprettyTyContext tyc <> line <> pretty "====================" <> line
    e <- ask
    E.printDiagnostic S.stdout True (not noColor) 4 E.defaultStyle diag 
    pc <- view pathCondition
    case pc of
      [] -> return ()
      _ -> putDoc' $ owlpretty "Path condition: " <> list (map owlpretty pc) <> line
    writeSMTCache
    -- Uncomment for debugging
    -- rs <- view tcRoutineStack
    -- logTypecheck $ owlpretty "Routines: " <> (mconcat $ L.intersperse (owlpretty ", ") $ map owlpretty rs)
    -- inds <- view inScopeIndices
    -- logTypecheck $ "Indices: " ++ show (owlprettyIndices inds)
    Check $ lift $ throwError e

------------------------------------------------------------
-- KDF scopes (docs/kdf-scopes.md)
------------------------------------------------------------

withKDFBinders :: ([IdxVar], [DataVar]) -> Ty -> Check a -> Check a
withKDFBinders (vs, xs) t k = 
    withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) vs) $ 
        withVars (map (\x -> (x, (ignore $ show x, Nothing, t))) xs) $ 
            local (set tcScope $ TcGhost False) k

-- Prove a proposition with the solver, without normalizing it first
kdfProves :: Prop -> Check Bool
kdfProves p = snd <$> (SMT.smtTypingQuery "kdf" $ SMT.symAssert p)

-- All names mentioned in an AExpr
aexprNames :: AExpr -> [NameExp]
aexprNames a = 
    case a^.val of
      AEApp _ fps as -> concatMap paramNames fps ++ concatMap aexprNames as
      AEGet n -> nameNames n
      AEGetEncPK n -> nameNames n
      AEGetVK n -> nameNames n
      AEKDF x y z _ _ -> concatMap aexprNames [x, y, z]
      _ -> []
    where
        paramNames (ParamAExpr x) = aexprNames x
        paramNames (ParamName n) = nameNames n
        paramNames _ = []
        nameNames n = n : case n^.val of
                            NameConst _ _ as -> concatMap aexprNames as
                            KEMName n' _ -> nameNames n'
                            KDFName (KDFRuleRef _ _ as) _ _ -> concatMap aexprNames as

-- The constants (function applications built from literals) in the given
-- terms are constants for the solver too, which knows that names miss them
kdfConstantFacts :: [AExpr] -> Check Prop
kdfConstantFacts as = do
    as' <- mapM (\a -> resolveANF a >>= normalizeAExpr) as
    return $ foldr pAnd pTrue $ map (mkSpanned . PIsConstant) $ aundup $ concatMap go as'
    where
        go a | isConstant a = case a^.val of
                                AEApp _ _ (_ : _) -> [a]
                                _ -> [] -- literals are constants already
             | otherwise = case a^.val of
                             AEApp _ _ xs -> concatMap go xs
                             AEKDF x y z _ _ -> concatMap go [x, y, z]
                             _ -> []

-- The salt and the ikm atoms of a case, normalized
kdfCaseAtoms :: KDFCase -> Check [AExpr]
kdfCaseAtoms (salt, ikm, _) = liftM2 (:) (normalizeAExpr salt) (unconcat ikm)

kdfRecIdx :: KDFRule -> Maybe IdxVar
kdfRecIdx rule = case _kdfCases rule of
                   KDFRecCases (IVar _ _ i) _ _ -> Just i
                   _ -> Nothing

-- The index that a reference puts at the recursion position of its (recursive) rule
kdfRefRecIdx :: KDFRuleRef -> Check (Maybe Idx)
kdfRefRecIdx (KDFRuleRef l (is, _) _) = do
    rd <- lookupKDFRule l
    let (((ixs, _), _), rule) = unsafeUnbind $ _kdfRuleBody rd
    return $ do
        i <- kdfRecIdx rule
        pos <- L.elemIndex i ixs
        listToMaybe $ drop pos is

-- Declaration-time checks for kdf_scope blocks
checkKDFScope :: String -> [Decl] -> Check a -> Check a
checkKDFScope scope ds cont = do
    ensureNoConcreteDefs
    forM_ ds $ \d -> withSpan (d^.spanOf) $ case d^.val of
        DeclName n b -> case snd (unsafeUnbind b) of
                          DeclBaseName (Spanned _ NT_DH) _ -> return ()
                          DeclBaseName (Spanned _ NT_KDF) _ -> return ()
                          DeclBaseName _ _ -> typeError $ "Only DH and kdfkey names are allowed in kdf_scope (bad type for '" ++ n ++ "')"
                          DeclAbstractName -> typeError $ "Abstract name declarations not allowed in kdf_scope: " ++ n
                          DeclAbbrev _ -> typeError $ "Name abbreviations not allowed in kdf_scope: " ++ n
        DeclDef _ _ -> typeError "def not allowed inside kdf_scope"
        DeclDefHeader _ _ -> typeError "def not allowed inside kdf_scope"
        DeclLocality _ _ -> typeError "locality not allowed inside kdf_scope"
        DeclModule _ _ _ _ -> typeError "module not allowed inside kdf_scope"
        DeclTable _ _ _ -> typeError "table not allowed inside kdf_scope"
        DeclKDFScope _ _ -> typeError "kdf_scope blocks cannot be nested"
        _ -> return ()
    let rules = [(l, b) | Spanned _ (DeclKDFRule l b) <- ds]
    existing <- view $ curMod . kdfRules
    assert ("Duplicate KDF rule labels: a label of kdf_scope '" ++ scope ++ "' is used twice, or is already used by an earlier kdf_scope") $ UL.allUnique (map fst rules ++ map fst existing)
    -- Rules may refer to later rules of the scope, so all of them are registered up front
    let ruleDefs = [(l, KDFRuleDef scope pos False b) | (pos, (l, b)) <- zip [0..] rules]
    let setChecked l = map (\(l', rd) -> if l == l' then (l', rd { _kdfRuleChecked = True }) else (l', rd))
    let go [] = cont
        go (d : ds') = withSpan (d^.spanOf) $ case d^.val of
            DeclName n _ -> checkDecl d $ local (over (curMod . kdfScopeNames) $ insert n scope) $ go ds'
            DeclKDFRule l _ -> do
                checkKDFRule l
                local (over (curMod . kdfRules) $ setChecked l) $ go ds'
            _ -> checkDecl d $ go ds'
    local (over (curMod . kdfRules) $ (++ ruleDefs)) $ do
        checkKDFRulesWellFounded rules
        go ds

-- Is ne a kdfkey of the scope: a base name declared in it, or derived by one of its rules
kdfIsScopeKey :: String -> NameExp -> Check Bool
kdfIsScopeKey scope ne = 
    case ne^.val of
      KDFName (KDFRuleRef l _ _) nks j -> do
          rd <- lookupKDFRule l
          return $ _kdfRuleScope rd == scope && j < length nks && nks !! j == NK_KDF
      NameConst _ _ _ -> do
          b <- kdfIsScopeName scope ne 
          nt <- getNameType ne
          return $ b && (nt^.val) `aeq` NT_KDF
      _ -> return False

-- Is ne a base name declared in the scope
kdfIsScopeName :: String -> NameExp -> Check Bool
kdfIsScopeName scope ne = do
    ne' <- normalizeNameExp ne
    case ne'^.val of
      NameConst _ (PRes (PDot p n)) _ -> do
          md <- openModule p
          return $ lookup n (md^.kdfScopeNames) == Just scope
      _ -> return False

pattern DHSecret :: NameExp -> NameExp -> AExprX
pattern DHSecret x y <- AEApp (PRes (PDot PTop "dh_combine")) _ [Spanned _ (AEApp (PRes (PDot PTop "dhpk")) _ [Spanned _ (AEGet x)]), Spanned _ (AEGet y)]

-- Declaration-time well-formedness checks for a KDF rule:
-- - parameters distinct and used, where clause is clean
-- - outputs are uniform
-- - input keys are from the scope
-- - cannot generate a key cycle
-- - self-disjointness and cross-disjointness
checkKDFRule :: String -> Check ()
checkKDFRule l = do
    pth <- (\p -> PRes $ PDot p l) <$> curModName
    rd <- lookupKDFRule pth
    let scope = _kdfRuleScope rd
    (((is, ps), xs), rule) <- unbind $ _kdfRuleBody rd
    assert ("Duplicate parameters in KDF rule '" ++ l ++ "'") $ UL.allUnique (map show (is ++ ps) ++ map show xs)
    withKDFBinders (is ++ ps, xs) tGhost $ do
        checkProp $ _kdfWhere rule
        -- The where clause selects instances by their parameters. Were it to depend on
        -- the execution (labels, events), the inputs of an instance would not determine
        -- which derived name it is (docs/kdf-scopes.md section 8).
        exec <- propMentionsExecution $ _kdfWhere rule
        assert ("The where clause of KDF rule '" ++ l ++ "' may not mention labels (sec, corr, or a flow) or events (happened, honest_pk_enc, honest_kem_encaps), directly or through a predicate") $ not exec
        assert ("KDF rule '" ++ l ++ "' must have an output") $ not $ null $ _kdfOutputs rule
        forM_ (_kdfOutputs rule) $ \(_, nt) -> do
            checkNameType nt
            nameTypeUniform nt
    insts <- kdfInsts pth
    hasDH <- forM insts $ \binst -> do
        (bnds@(vs, xs'), inst) <- unbind binst
        withKDFBinders bnds tGhost $ do
            let (salt, ikm, info) = _kiCase inst
            mapM_ inferAExpr [salt, ikm, info]
            -- References to rules must be visible in the rule itself (for checkKDFRulesWellFounded)
            hidden <- concatMap aexprNames <$> mapM normalizeAExpr [salt, ikm, info]
            let visible = [m | Spanned _ (KDFName (KDFRuleRef m _ _) _ _) <- concatMap aexprNames [salt, ikm, info]]
            forM_ [m | Spanned _ (KDFName (KDFRuleRef m _ _) _ _) <- hidden] $ \m -> 
                assert ("KDF rule '" ++ l ++ "' refers to rule '" ++ show (owlpretty m) ++ "' through a function; write the reference to that rule in the rule itself") $ any (aeq m) visible
            -- Every parameter is bound in the inputs
            let unused = [show v | v <- vs, not $ v `elem` (toListOf fv (_kiCase inst) :: [IdxVar])]
                      ++ [show x | x <- xs', not $ x `elem` (toListOf fv (_kiCase inst) :: [DataVar])]
            assert ("Parameters of KDF rule '" ++ l ++ "' must appear in its salt, ikm, or info: " ++ L.intercalate ", " unused) $ null unused
            -- The case is bound to the scope by one of its keys
            atoms <- kdfCaseAtoms (_kiCase inst)
            bound <- forM atoms $ \a -> case a^.val of
                AEGet n -> do
                    b <- kdfIsScopeKey scope n
                    assert ("The name " ++ show (owlpretty n) ++ " is used as a key by KDF rule '" ++ l ++ "', so it must be a kdfkey of kdf_scope '" ++ scope ++ "'") b
                    return True
                DHSecret x y -> do
                    bx <- kdfIsScopeName scope x
                    by <- kdfIsScopeName scope y
                    assert ("Both DH names of " ++ show (owlpretty a) ++ " must belong to kdf_scope '" ++ scope ++ "'") $ bx && by
                    return True
                _ -> return False
            assert ("KDF rule '" ++ l ++ "' must have a kdfkey or a DH secret of kdf_scope '" ++ scope ++ "' as its salt or as an atom of its ikm") $ or bound
            return $ or [True | Spanned _ (DHSecret _ _) <- atoms]
    -- A rule that relies on the ODH assumption says so
    assert ("KDF rule '" ++ l ++ "' has a DH secret in its ikm, so it must be declared with odh") $ not (or hasDH) || _kdfIsODH rule
    checkKDFOutputsAcyclic pth
    -- Disjointness: from itself, and from the rules checked so far
    forM_ [(a, b, ia == ib) | (ia, a) <- zip [0 :: Int ..] insts, (ib, b) <- zip [0..] insts, ia <= ib] $ \(a, b, sameCase) -> do
        disj <- kdfDisjoint a b sameCase
        assert ("KDF rule '" ++ l ++ "' overlaps with itself: two of its instances with distinct parameters may have the same salt, ikm, and info. Separate its instances with a where clause or a distinguishing constant in the info") disj
    others <- kdfScopeRules pth
    forM_ others $ \pth' -> do
        insts' <- kdfInsts pth'
        forM_ [(a, b) | a <- insts, b <- insts'] $ \(a, b) -> do
            disj <- kdfDisjoint a b False
            assert ("KDF rule '" ++ l ++ "' overlaps with rule '" ++ show (owlpretty pth') ++ "': an instance of each may have the same salt, ikm, and info. Separate the two rules with a where clause or a distinguishing constant in the info") disj

-- Does a proposition depend on the path condition rather than on its free variables
-- alone: a flow between labels, or an event (happened, honest_pk_enc,
-- honest_kem_encaps), directly, through a predicate, or through the AAD
-- predicate of a name?
propMentionsExecution :: Prop -> Check Bool
propMentionsExecution p = case p^.val of
    PFlow _ _ -> return True
    PHappened _ _ _ -> return True
    PHonestPKEnc _ _ -> return True
    PHonestKEMEncaps _ _ -> return True
    PAnd p1 p2 -> liftM2 (||) (propMentionsExecution p1) (propMentionsExecution p2)
    POr p1 p2 -> liftM2 (||) (propMentionsExecution p1) (propMentionsExecution p2)
    PImpl p1 p2 -> liftM2 (||) (propMentionsExecution p1) (propMentionsExecution p2)
    PNot p1 -> propMentionsExecution p1
    PLetIn a xp -> do
        (x, p') <- unbind xp
        propMentionsExecution $ subst x a p'
    PQuantIdx _ _ ip -> do
        (i, p') <- unbind ip
        withIndices [(i, (ignore $ show i, IdxGhost))] $ propMentionsExecution p'
    PQuantBV _ _ xp -> do
        (x, p') <- unbind xp
        withVars [(x, (ignore $ show x, Nothing, tGhost))] $ propMentionsExecution p'
    PApp s is xs -> extractPredicate s is xs >>= propMentionsExecution
    PAADOf ne a -> extractAAD ne a >>= propMentionsExecution
    _ -> return False

-- The checked rules in the scope of a rule
kdfScopeRules :: Path -> Check [Path]
kdfScopeRules l@(PRes pth) = do
    rd <- lookupKDFRule l
    rules <- collectKDFRules
    return [PRes pth' | (pth', rd') <- rules, _kdfRuleChecked rd', _kdfRuleScope rd' == _kdfRuleScope rd, 
                        pathPrefix pth' `aeq` pathPrefix pth]

kdfRefParamsEq :: KDFRuleRef -> KDFRuleRef -> Prop
kdfRefParamsEq (KDFRuleRef _ (is1, ps1) as1) (KDFRuleRef _ (is2, ps2) as2) = 
    foldr pAnd pTrue $ zipWith (\i j -> mkSpanned $ PEqIdx i j) (is1 ++ ps1) (is2 ++ ps2) ++ zipWith pEq as1 as2

-- Two cases are disjoint when no instance of one has the salt, ikm, and info of
-- an instance of the other, while either is applicable. For two instances of
-- the same case, this is required of distinct instances only. 
kdfDisjoint :: Bind ([IdxVar], [DataVar]) KDFInst -> Bind ([IdxVar], [DataVar]) KDFInst -> Bool -> Check Bool
kdfDisjoint ba bb sameCase = do
    (bndsA, a) <- unbind ba
    (bndsB, b) <- unbind bb
    if sameCase && null (fst bndsA) && null (snd bndsA) then return True else
      withKDFBinders (fst bndsA ++ fst bndsB, snd bndsA ++ snd bndsB) (tData advLbl advLbl) $ do
        -- Names in key positions are compared as names: two derived names are
        -- equal only if they are the same instance of the same rule, and a
        -- derived name is not a base name. Across rules and against base names
        -- this is assumed without a guard (docs/kdf-scopes.md section 8).
        atomsA <- kdfCaseAtoms (_kiCase a)
        atomsB <- kdfCaseAtoms (_kiCase b)
        let identity = [ fact | Spanned _ (AEGet n1) <- atomsA, Spanned _ (AEGet n2) <- atomsB,
                                fact <- case (n1^.val, n2^.val) of
                                  (KDFName r1@(KDFRuleRef l1 _ _) _ _, KDFName r2@(KDFRuleRef l2 _ _) _ _)
                                      | l1 `aeq` l2 -> [pImpl (pEq (aeGet n1) (aeGet n2)) (kdfRefParamsEq r1 r2)]
                                      | otherwise -> [pNot $ pEq (aeGet n1) (aeGet n2)]
                                  (KDFName _ _ _, NameConst _ _ _) -> [pNot $ pEq (aeGet n1) (aeGet n2)]
                                  (NameConst _ _ _, KDFName _ _ _) -> [pNot $ pEq (aeGet n1) (aeGet n2)]
                                  _ -> [] ]
        let ((saltA, ikmA, infoA), (saltB, ikmB, infoB)) = (_kiCase a, _kiCase b)
        constants <- kdfConstantFacts [saltA, ikmA, infoA, saltB, ikmB, infoB]
        let overlap = foldr pAnd pTrue $
                [_kiWhere a, _kiWhere b, pOr (_kiApp a) (_kiApp b), constants] ++ identity ++
                [pEq saltA saltB, pEq ikmA ikmB, pEq infoA infoB] ++
                [pNot $ kdfRefParamsEq (_kiRef a) (_kiRef b) | sameCase]
        kdfProves $ pNot overlap

-- References between rule instances must have no infinite chain, so that every
-- derived name is defined by induction from base names. Within a group of
-- mutually recursive rules, every reference must decrease the pair
-- (recursion index, position of the rule) lexicographically.
checkKDFRulesWellFounded :: [(String, Bind KDFRuleParams KDFRule)] -> Check ()
checkKDFRulesWellFounded rules = do
    cur <- curModName
    let labelOf (PRes (PDot p l)) | p `aeq` cur = Just l
        labelOf _ = Nothing
    -- Edges L -> M, with the index at M's recursion position and the case of L it occurs in
    edges <- fmap concat $ forM rules $ \(l, b) -> do
        (((is, ps), xs), rule) <- unbind b
        cases <- case _kdfCases rule of
                   KDFOneCase c -> return [(c, Nothing, [])]
                   KDFRecCases (IVar _ _ i) c0 bc1 -> do
                       (i', c1) <- unbind bc1
                       return [(c0, Just (i, Nothing), []), (c1, Just (i, Just i'), [i'])]
                   _ -> typeError $ "Internal: recursion index of KDF rule '" ++ l ++ "' is not a variable"
        fmap concat $ forM cases $ \((salt, ikm, info), recInfo, extra) -> 
            -- References are read off the syntax of the rule (checkKDFRule makes sure that no function hides one)
            withKDFBinders (is ++ ps ++ extra, xs) tGhost $ do
                fmap concat $ forM [r | Spanned _ (KDFName r _ _) <- concatMap aexprNames [salt, ikm, info]] $ \r@(KDFRuleRef m _ _) -> 
                    case labelOf m of
                      Just m' | m' `elem` map fst rules -> do
                          e <- kdfRefRecIdx r
                          return [(l, m', e, recInfo)]
                      _ -> return []
    let pos l = fromJust $ L.elemIndex l (map fst rules)
    -- Rules that reach each other
    let reach l = go [] [m | (l', m, _, _) <- edges, l' == l]
            where go seen [] = seen
                  go seen (m : ms) | m `elem` seen = go seen ms
                                   | otherwise = go (m : seen) ([m' | (l', m', _, _) <- edges, l' == m] ++ ms)
    forM_ edges $ \(l, m, e, recInfo) -> when (l `elem` reach m) $ do
        let isVar v i = case i of 
                          IVar _ _ v' -> v == v'
                          _ -> False
        let ok = case (recInfo, e) of
                   -- from the succ case (recursion index i = succ(i'))
                   (Just (i, Just i'), Just e') -> 
                       isVar i' e' || e' `aeq` IZero || ((isVar i e' || e' `aeq` ISucc (mkIVar i')) && pos m < pos l)
                   -- from the zero case (i = 0)
                   (Just (i, Nothing), Just e') -> (e' `aeq` IZero || isVar i e') && pos m < pos l
                   _ -> False
        let msg = case (recInfo, e) of
                    (Nothing, _) -> "KDF rule '" ++ l ++ "' refers to rule '" ++ m ++ "' under mutual recursion, but is not a rec_kdf/rec_odh rule"
                    (_, Nothing) -> "KDF rule '" ++ l ++ "' refers to rule '" ++ m ++ "' under mutual recursion, but '" ++ m ++ "' is not a rec_kdf/rec_odh rule"
                    (Just (_, Just _), Just e') -> "KDF rule '" ++ l ++ "' refers to rule '" ++ m ++ "' at index '" ++ show (owlpretty e') ++ "' of its recursion slot, which does not decrease the rank (index, declaration position): in the succ case, use the predecessor index or 0 for any rule, or the recursion index for a rule declared earlier"
                    (Just (_, Nothing), Just e') -> "KDF rule '" ++ l ++ "' refers to rule '" ++ m ++ "' at index '" ++ show (owlpretty e') ++ "' of its recursion slot, which does not decrease the rank (index, declaration position): in the zero case, use 0 or the recursion index for a rule declared earlier"
        assert msg ok

-- The output types of a rule must not close a key cycle: in a plaintext
-- position, they may not mention a base name the rule is derived from, nor a
-- derived name the rule is derived from.
checkKDFOutputsAcyclic :: Path -> Check ()
checkKDFOutputsAcyclic pth = do
    rd <- lookupKDFRule pth
    -- Names in the inputs of a rule
    let inputsOf l = do
            insts <- kdfInsts l
            fmap concat $ forM insts $ \binst -> do
                (bnds, inst) <- unbind binst
                let (salt, ikm, info) = _kiCase inst
                withKDFBinders bnds tGhost $ concatMap aexprNames <$> mapM normalizeAExpr [salt, ikm, info]
    let down seen [] = return seen
        down seen (l : ls) | any (aeq l) seen = down seen ls
                           | otherwise = do
                               ns <- inputsOf l
                               down (l : seen) ([m | Spanned _ (KDFName (KDFRuleRef m _ _) _ _) <- ns] ++ ls)
    below <- down [] [pth]
    inputs <- concat <$> mapM inputsOf below
    above <- forM below $ \m -> (,) m <$> down [] [m]
    (((is, ps), xs), rule) <- unbind $ _kdfRuleBody rd
    withKDFBinders (is ++ ps, xs) tGhost $ forM_ (zip [0 :: Int ..] $ _kdfOutputs rule) $ \(j, (_, nt)) -> do
        ns <- nameTypePlaintextNames nt
        -- The outputs of one instance are ordered: output j may mention only later ones
        let laterSibling j' = assert ("KDF rule '" ++ show (owlpretty pth) ++ "': output " ++ show j ++ " mentions output " ++ show j' ++ " of the same instance (outputs are numbered from 0), which may form a key cycle; an output may mention only later outputs of its instance") $ j' > j
        forM_ ns $ \ne -> case ne^.val of
            KDFName r@(KDFRuleRef m (mis, mps) mas) _ j'
                | not (any (aeq m) below) -> return ()
                -- A sibling output of the same instance
                | m `aeq` pth && isNothing (kdfRecIdx rule) && 
                    (mis ++ mps) `aeq` map mkIVar (is ++ ps) && mas `aeq` map aeVar' xs -> laterSibling j'
                | otherwise -> do
                    -- Under mutual recursion: a later instance
                    e <- kdfRefRecIdx r
                    rdm <- lookupKDFRule m
                    let succs i = case i of
                                    ISucc i' -> fmap (+ 1) (succs i')
                                    IVar _ _ v | Just v == kdfRecIdx rule -> Just (0 :: Int)
                                    _ -> Nothing
                    let sameGroup = any (aeq pth) $ concat [ms | (m', ms) <- above, m' `aeq` m]
                    -- At the same index: a later rule of the group, or the rule itself,
                    -- where the outputs of the instances at that index are ordered
                    let ok = case e >>= succs of
                               Just n -> sameGroup && (n >= 1 || m `aeq` pth || _kdfRulePos rdm > _kdfRulePos rd)
                               Nothing -> False
                    when (ok && m `aeq` pth && (e >>= succs) == Just 0) $ laterSibling j'
                    assert ("KDF rule '" ++ show (owlpretty pth) ++ "': output type mentions derived name " ++ show (owlpretty ne) ++ ", which is (transitively) an input of the rule: a key derived from a name may not encrypt, sign or MAC that name (key cycle); under mutual recursion, the index at the recursion slot must be succ^n(i) with n >= 1, or i for a rule declared after '" ++ show (owlpretty pth) ++ "'") ok
            NameConst _ p _ -> 
                assert ("KDF rule '" ++ show (owlpretty pth) ++ "': output type mentions name " ++ show (owlpretty ne) ++ ", which is (transitively) an input of the rule: a key derived from a name may not encrypt, sign or MAC that name (key cycle)") $ 
                    not $ or [p `aeq` p' | Spanned _ (NameConst _ p' _) <- inputs]
            _ -> return ()

-- Names in the plaintext positions of a name type. Called on rule outputs,
-- which should be uniform; any other name type is a bug.
nameTypePlaintextNames :: NameType -> Check [NameExp]
nameTypePlaintextNames nt =
    case nt^.val of
      NT_Enc t -> tyNames t
      NT_StAEAD t _ _ _ -> tyNames t
      NT_PKE t -> tyNames t
      NT_MAC t -> tyNames t
      NT_Sig t -> tyNames t
      NT_App p ps as -> resolveNameTypeApp p ps as >>= nameTypePlaintextNames
      NT_Nonce _ -> return []
      NT_KDF -> return []
      _ -> typeError $ "Internal error: called nameTypePlaintextNames on an invalid name type " ++ show (owlpretty nt) ++ ". This is a bug in the Owl typechecker"
    where
        nameNames n = aexprNames (aeGet n)
        labelNames l = case l^.val of
            LName n -> nameNames n
            LJoin l1 l2 -> labelNames l1 ++ labelNames l2
            LRangeIdx b -> labelNames $ snd $ unsafeUnbind b
            LRangeVar b -> labelNames $ snd $ unsafeUnbind b
            _ -> []
        propNames p = case p^.val of
            PAnd p1 p2 -> propNames p1 ++ propNames p2
            POr p1 p2 -> propNames p1 ++ propNames p2
            PImpl p1 p2 -> propNames p1 ++ propNames p2
            PNot p1 -> propNames p1
            PEq a b -> aexprNames a ++ aexprNames b
            PLetIn a b -> aexprNames a ++ propNames (snd $ unsafeUnbind b)
            PFlow l1 l2 -> labelNames l1 ++ labelNames l2
            PHappened _ _ as -> concatMap aexprNames as
            PQuantIdx _ _ b -> propNames $ snd $ unsafeUnbind b
            PQuantBV _ _ b -> propNames $ snd $ unsafeUnbind b
            PIsConstant a -> aexprNames a
            PApp _ _ as -> concatMap aexprNames as
            PAADOf n a -> nameNames n ++ aexprNames a
            PHonestPKEnc n a -> nameNames n ++ aexprNames a
            PHonestKEMEncaps n a -> nameNames n ++ aexprNames a
            _ -> []
        paramNames fp = case fp of
            ParamAExpr a -> return $ aexprNames a
            ParamLbl l -> return $ labelNames l
            ParamTy t -> tyNames t
            ParamName n -> return $ nameNames n
            _ -> return []
        -- Every name a value of the type may depend on: refinements, labels,
        -- and case conditions count, since the payload may be the name itself
        tyNames t = case t^.val of
            TName n -> return $ nameNames n
            TSS n m -> return $ nameNames n ++ nameNames m
            TData l1 l2 _ -> return $ labelNames l1 ++ labelNames l2
            TDataWithLength l a -> return $ labelNames l ++ aexprNames a
            TBool l -> return $ labelNames l
            TRefined t' _ xp -> (++ propNames (snd $ unsafeUnbind xp)) <$> tyNames t'
            TOption t' -> tyNames t'
            TCase p t1 t2 -> (propNames p ++) <$> liftM2 (++) (tyNames t1) (tyNames t2)
            TExistsIdx _ bt -> do
                (i, t') <- unbind bt
                withIndices [(i, (ignore $ show i, IdxGhost))] $ tyNames t'
            TConst s ps -> (++) <$> (concat <$> mapM paramNames ps) <*> do
                td <- getTyDef s
                case td of
                  TyAbbrev t' -> tyNames t'
                  EnumDef b -> do
                      bdy <- extractEnum ps (show s) b
                      concat <$> mapM tyNames (catMaybes $ map snd bdy)
                  StructDef b -> do
                      idxs <- getStructParams ps
                      (is, dp) <- unbind b
                      let go d = case d of
                                   DPDone _ -> return []
                                   DPVar t' _ xd -> do
                                       (x, d') <- unbind xd
                                       liftM2 (++) (tyNames t') (withVars [(x, (ignore $ show x, Nothing, t'))] $ go d')
                      if length is == length idxs then go (substs (zip is idxs) dp) else return []
                  TyAbstract -> return []
            _ -> return []

-- kdf<hints; nks; j>(salt, ikm, info)
checkKDFCall :: [KDFRuleRef] -> [NameKind] -> Int -> (AExpr, Ty) -> (AExpr, Ty) -> (AExpr, Ty) -> Check Ty
checkKDFCall hints nks j (a, ta) (b, tb) (c, tc) = do
    assert ("KDF output index " ++ show j ++ " out of bounds: the call declares " ++ show (length nks) ++ " output(s)") $ j < length nks
    [a', b', c'] <- mapM resolveANF [a, b, c]
    let refine t = tRefined t ".res" $ 
            pAnd (pEq (aeLength (aeVar ".res")) (nameKindLength $ nks !! j))
                 (pEq (aeVar ".res") $ mkSpanned $ AEKDF a' b' c' nks j)
    atoms <- unconcat b
    apub <- tyFlowsTo ta advLbl
    bpubs <- mapM kdfAtomPublic atoms
    cpub <- tyFlowsTo tc advLbl
    -- A KDF of public inputs is fully public
    if apub && and bpubs && cpub then return $ refine $ tData advLbl advLbl else local (set tcScope $ TcGhost False) $ do
        assert "The info of a KDF call must be public" cpub
        assert "A KDF call without hints must have public arguments" $ not $ null hints
        hintRules <- forM hints $ \h@(KDFRuleRef l _ _) -> do
            (rd, rule) <- instKDFRule h
            nks' <- mapM (getNameKind . snd) (_kdfOutputs rule)
            kdfCheckHintArgs h
            assert ("KDF call declares outputs " ++ show (owlpretty $ NameKindRow nks) ++ " but rule '" ++ show (owlpretty l) ++ "' has outputs " ++ show (owlpretty $ NameKindRow nks')) $ nks == nks'
            return (h, rd, rule)
        let scope = _kdfRuleScope $ (\(_, rd, _) -> rd) $ head hintRules
        assert "All hints of a KDF call must belong to the same kdf_scope" $ all (\(_, rd, _) -> _kdfRuleScope rd == scope) hintRules
        constants <- kdfConstantFacts [a', b', c']
        let matchProp inst = let (salt, ikm, info) = _kiCase inst in
                foldr pAnd pTrue [_kiWhere inst, _kiApp inst, pEq a' salt, pEq b' ikm, pEq c' info]
        -- A hint matches when its instance is applicable and the call's arguments match the instance's salt, ikm, and info
        matches <- flip filterM hintRules $ \(h, _, _) -> do
            oinst <- kdfInstAt h
            case oinst of
              Nothing -> return False
              Just inst -> kdfProves $ matchProp inst
        -- Every non-public input to the kdf call must be a key from the hint's scope (whether or not it matches)
        oks <- forM (zip (a' : atoms) (apub : bpubs)) $ \(x, pub) -> if pub then return True else kdfIsScopeKeyInput scope x
        case [x | (x, False) <- zip (a' : atoms) oks] of
          x : _ -> typeError $ "KDF call: component " ++ show (owlpretty x) ++ " is neither public nor a kdfkey or DH secret of kdf_scope '" ++ scope ++ "' in a key position"
          [] -> return ()
        case matches of
          (h, _, rule) : _ -> do
              let ne = mkSpanned $ KDFName h nks j
              return $ refine $ case fst (_kdfOutputs rule !! j) of
                         KDFStrict -> tRefined (tName ne) ".res" $ pSec ne
                         KDFPub -> tRefined (tName ne) ".res" $ pFlow (nameLbl ne) advLbl
                         KDFUnstrict -> tName ne
          [] -> do
              -- Otherwise the call must not match any applicable instance of any rule of the scope
              let KDFRuleRef l0 _ _ = head hints
              rules <- kdfScopeRules l0
              cases <- fmap concat $ forM rules $ \l -> do
                  insts <- kdfInsts l >>= fmap concat . mapM kdfSplitRecIndices
                  forM insts $ \binst -> do
                      ((vs, xs), inst) <- unbind binst
                      let (salt, ikm, info) = _kiCase inst
                      constants' <- withKDFBinders (vs, xs) tGhost $ kdfConstantFacts [salt, ikm, info]
                      let noMatch = mkForallIdx vs $ foldr (\x p -> mkSpanned $ PQuantBV Forall (ignore $ show x) $ bind x p) 
                                        (pNot $ foldr pAnd pTrue [constants, constants', matchProp inst]) xs
                      return (l, noMatch)
              -- One query for all rules. If it fails, find a rule to blame
              refuted <- kdfProves $ foldr pAnd pTrue $ map snd cases
              when (not refuted) $ do
                  forM_ cases $ \(l, noMatch) -> do
                      b <- kdfProves noMatch
                      assert ("Inconclusive: cannot match this KDF call with one of its hints, or prove that it matches no instance of rule '" ++ show (owlpretty l) ++ "'. If the rule is excluded only because a public value differs from a secret name or DH secret, try calling secret_neq_lemma(<public value>, <secret>) before this call") b
                  typeError $ "Inconclusive: cannot match this KDF call with one of its hints, or prove that it matches no rule of kdf_scope '" ++ scope ++ "', although each rule is refuted separately. This likely indicates incompleteness in the typechecker"
              return $ refine $ tData advLbl advLbl

-- A parameter used as the base of a DH computation dh_combine(x, get(N)) stands
-- for an adversarial group element: that atom is never a key position. An
-- honest DH secret must be written dh_ss(A, B) in the rule, so a hint may not
-- pass an honest public key for such a parameter.
kdfCheckHintArgs :: KDFRuleRef -> Check ()
kdfCheckHintArgs (KDFRuleRef l _ as) = do
    insts <- kdfInsts l
    forM_ insts $ \binst -> do
        ((vs, xs), inst) <- unbind binst
        atoms <- withKDFBinders (vs, xs) tGhost $ kdfCaseAtoms (_kiCase inst)
        let bases = [x | Spanned _ (AEApp (PRes (PDot PTop "dh_combine")) _ [Spanned _ (AEVar _ x), _]) <- atoms]
        forM_ (zip xs as) $ \(x, arg) -> when (x `elem` bases) $ do
            t <- inferAExpr arg >>= normalizeTy
            case (stripRefinements t)^.val of
              TDH_PK _ -> typeError $ "The hint passes the honest public key " ++ show (owlpretty arg) ++ " for a parameter used as a DH base in rule '" ++ show (owlpretty l) ++ "'; use a rule with dh_ss instead"
              _ -> return ()

-- An ikm atom is public if its type is public, or if it is a DH secret with a corrupt exponent
kdfAtomPublic :: AExpr -> Check Bool
kdfAtomPublic x = do
    t <- inferAExpr x >>= normalizeTy
    pub <- tyFlowsTo t advLbl
    if pub then return True else 
        case (stripRefinements t)^.val of
          TSS n m -> kdfProves $ pOr (pFlow (nameLbl n) advLbl) (pFlow (nameLbl m) advLbl)
          _ -> return False

-- A key of the scope in a key position: a kdfkey from the scope, or a DH
-- computation with an exponent from the scope
kdfIsScopeKeyInput :: String -> AExpr -> Check Bool
kdfIsScopeKeyInput scope x = do
    t <- inferAExpr x >>= normalizeTy
    byTy <- goTy t
    if byTy then return True else 
        case x^.val of
          AEApp (PRes (PDot PTop "dh_combine")) _ [y, z] -> do
              tz <- inferAExpr z >>= normalizeTy
              case (stripRefinements tz)^.val of
                TName n -> kdfIsScopeName scope n
                _ -> return False
          _ -> return False
    where
        goTy t = case (stripRefinements t)^.val of
                   TName n -> kdfIsScopeKey scope n
                   TSS n m -> liftM2 (||) (kdfIsScopeName scope n) (kdfIsScopeName scope m)
                   TCase p t1 t2 -> do
                       ob <- decideProp p
                       case ob of
                         Just True -> goTy t1
                         Just False -> goTy t2
                         Nothing -> liftM2 (&&) (goTy t1) (goTy t2)
                   _ -> tyFlowsTo t advLbl

-- Used when refuting a call. If a case uses a recursive rule at one of its own
-- index variables i, the solver knows nothing about that value, so split the
-- case into i = 0 and i = succ(i').
kdfSplitRecIndices :: Bind ([IdxVar], [DataVar]) KDFInst -> Check [Bind ([IdxVar], [DataVar]) KDFInst]
kdfSplitRecIndices binst = do
    ((vs, xs), inst) <- unbind binst
    atoms <- withKDFBinders (vs, xs) tGhost $ kdfCaseAtoms (_kiCase inst)
    recIdxs <- forM [r | Spanned _ (KDFName r _ _) <- concatMap aexprNames atoms] $ \r@(KDFRuleRef l _ _) -> do
        cases <- kdfInsts l
        if length cases > 1 then kdfRefRecIdx r else return Nothing
    case [v | Just (IVar _ _ v) <- recIdxs, v `elem` vs] of
      [] -> return [binst]
      (v : _) -> do
          v' <- fresh v
          let others = filter (/= v) vs
          return [bind (others, xs) (subst v IZero inst), bind (v' : others, xs) (subst v (ISucc $ mkIVar v') inst)]

---- Lemmas about KDFs and DH

-- For every DH secret dh_ss(A, B) of the scope of N, and public x: if N is
-- secret and is neither A nor B, then x^N is not that secret. (Given g^x, y,
-- and z, it is hard to construct h such that h^x = g^(y * z).)
crossDHLemma :: NameExp -> [(AExpr, Ty)] -> Check Ty
crossDHLemma n args = do
    assert ("Wrong number of arguments to cross_dh_lemma") $ length args == 1
    let [(x, t)] = args
    b <- tyFlowsTo t advLbl
    assert ("Argument to cross_dh_lemma must flow to adv") b
    nt <- getNameType n
    assert ("Name parameter to cross_dh_lemma must be a DH name") $ (nt^.val) `aeq` NT_DH
    rules <- collectKDFRules
    inScope <- filterM (\(_, rd) -> kdfIsScopeName (_kdfRuleScope rd) n) [r | r <- rules, _kdfRuleChecked (snd r)]
    ps <- fmap concat $ forM inScope $ \(pth, _) -> do
        insts <- kdfInsts (PRes pth)
        fmap concat $ forM insts $ \binst -> do
            ((vs, xs), inst) <- unbind binst
            withKDFBinders (vs, xs) tGhost $ do
                atoms <- kdfCaseAtoms (_kiCase inst)
                forM [(n2, n3) | Spanned _ (DHSecret n2 n3) <- atoms] $ \(n2, n3) -> do
                    n_disj <- liftM2 pAnd (pNot <$> pNameExpEq n n2) (pNot <$> pNameExpEq n n3)
                    return $ mkForallIdx vs $ pImpl (n_disj `pAnd` pSec n) $
                        pNot $ pEq (aeDHCombine x $ aeGet n) (aeDHCombine (aeDHPK $ aeGet n2) (aeGet n3))
    p <- normalizeProp $ foldr pAnd pTrue $ aundup ps
    return $ tLemma p

-- For public y, a base DH name s, and a base name n (whose indices may be
-- omitted, and are then quantified): if s is secret and n is not s, then y^s
-- is not n. If n is secret it is uniform; if it is public, this is inverse DH.
dhExpLemma :: NameExp -> NameExp -> [(AExpr, Ty)] -> Check Ty
dhExpLemma s n args = do
    assert ("Wrong number of arguments to dh_exp_lemma") $ length args == 1
    let [(y, t)] = args
    b <- tyFlowsTo t advLbl
    assert ("Argument to dh_exp_lemma must flow to adv") b
    case s^.val of
      NameConst _ _ _ -> return ()
      _ -> typeError $ "The exponent of dh_exp_lemma must be a base name: " ++ show (owlpretty s)
    nt <- getNameType s
    assert ("The exponent of dh_exp_lemma must be a base name of name type DH: " ++ show (owlpretty s)) $ (nt^.val) `aeq` NT_DH
    (qs, n') <- case n^.val of
        NameConst ([], []) pth@(PRes (PDot p nm)) [] -> do
            md <- openModule p
            case lookup nm (md^.nameDefs) of
              Just bnd -> do
                  let ((is, ps), _) = unsafeUnbind bnd
                  is' <- mapM fresh is
                  ps' <- mapM fresh ps
                  return (is' ++ ps', mkSpanned $ NameConst (map mkIVar is', map mkIVar ps') pth [])
              Nothing -> typeError $ show $ ErrUnknownName pth
        NameConst _ _ [] -> return ([], n)
        _ -> typeError $ "The target of dh_exp_lemma must be a base name: " ++ show (owlpretty n)
    local (set tcScope $ TcGhost False) $ withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) qs) $ do
        _ <- getNameType n'
        return ()
    return $ tLemma $ mkForallIdx qs $ 
        pImpl (pSec s `pAnd` (pNot $ pEq (aeGet n') (aeGet s))) 
              (pNot $ pEq (aeDHCombine y (aeGet s)) (aeGet n'))

-- The label of a derived name follows its rule instance: it is secret only if
-- the instance is applicable, and a strict output of an applicable instance is secret.
kdfLabelLemma :: NameExp -> Check Prop
kdfLabelLemma ne = local (set tcScope $ TcGhost False) $ 
    case ne^.val of
      KDFName r@(KDFRuleRef l _ _) _ j -> do
          _ <- getNameType ne
          (_, rule) <- instKDFRule r
          oinst <- kdfInstAt r
          case oinst of
            Nothing -> typeError $ "kdf_label_lemma: the case of " ++ show (owlpretty ne) ++ " is not determined by its index, and the zero and succ cases of rule '" ++ show (owlpretty l) ++ "' differ; use an index of the form 0 or succ(..)"
            Just inst -> do
                let app = _kiWhere inst `pAnd` _kiApp inst
                return $ case fst (_kdfOutputs rule !! j) of
                           KDFStrict -> pImpl (pSec ne) app `pAnd` pImpl app (pSec ne)
                           _ -> pImpl (pSec ne) app
      _ -> typeError $ "kdf_label_lemma: expected a derived name KDF<...>, got " ++ show (owlpretty ne)

-- Can the adversary compute x? Yes if its type is public, if it is a DH secret
-- with a corrupt exponent, or if it is a gkdf term whose inputs are all
-- computable (a gkdf term is typed Ghost, so its inputs are checked instead).
isAdvComputable :: AExpr -> Check Bool
isAdvComputable x0 = do
    x <- resolveANF x0 >>= normalizeAExpr
    b <- kdfAtomPublic x
    if b then return True else case x^.val of
      AEKDF a b' c _ _ -> do
          atoms <- unconcat b'
          bs <- mapM isAdvComputable $ [a] ++ atoms ++ [c]
          return $ and bs
      _ -> return False

-- secret_neq_lemma(x, w): a value the adversary can compute is not a secret.
-- One argument must be public. Each atom of the other that is a name, or a
-- DH secret of two base names, gives: if the atom is secret, x != w.
secretNeqLemma :: AExpr -> AExpr -> Check Prop
secretNeqLemma x0 w0 = do
    x <- resolveANF x0 >>= normalizeAExpr
    w <- resolveANF w0 >>= normalizeAExpr
    xpub <- isAdvComputable x
    wpub <- if xpub then return False else isAdvComputable w
    -- Neither public: no fact, and no error. The call is checked in every
    -- branch of the enclosing case splits, and in some the value is a name.
    let targets = [w | xpub] ++ [x | wpub]
    atomss <- mapM unconcat targets
    let isBase n = case n^.val of
                     NameConst _ _ _ -> True
                     _ -> False
    let facts = concat $ flip map (concat atomss) $ \a -> case a^.val of
                  AEGet n -> [pImpl (pSec n) (pNot $ pEq x w)]
                  DHSecret m n | isBase m && isBase n ->
                      [pImpl (pSec m `pAnd` pSec n) (pNot $ pEq x w)]
                  _ -> []
    return $ foldr pAnd pTrue facts
