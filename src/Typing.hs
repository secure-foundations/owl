{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module Typing where
import AST
import qualified Data.Map.Strict as M
import Error.Diagnose.Position (Position)
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

emptyModDef :: ModDef
emptyModDef = ModDef mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty 

-- extend with new parts of Env -- ok
emptyEnv :: Flags -> IO Env
emptyEnv f = do
    r <- newIORef 0
    return $ Env f initDetFuncs initDistrs mempty TcGhost mempty mempty mempty [(Nothing, emptyModDef)] interpUserFunc r


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

symCases :: Ty -> (Ty -> Check TyX) -> Check TyX
symCases t k =
    case t^.val of
      TCase p t1 t2 -> do
          t1' <- symCases t1 k
          t2' <- symCases t2 k
          return $ TCase p (mkSpanned t1') (mkSpanned t2')
      _ -> k t

mkSymCheck :: [Ty] -> ([Ty] -> Check TyX) -> Check TyX
mkSymCheck [] k = k []
mkSymCheck (t:ts) k =
    symCases t $ \t' ->
        mkSymCheck ts $ \ts' ->
            k (t' : ts')

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
mkSimpleFunc s i k = (s, (i, withNoParams s (\args -> mkSymCheck (map snd args) k)))

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
              let tr = aeApp (topLevelPath $ "TRUE") [] []
              return $ TRefined (mkSpanned $ TBool $ joinLbl l1 l2) (bind (s2n ".res") $ pImpl (pEq (aeVar ".res") tr) (pEq a1 a2))
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
    mkSimpleFunc "dh_combine" 2 $ \args ->
        case args of
          [t1, t2] | Just n <- extractDHPKFromType t1, Just m <- extractNameFromType t2 -> do
              nt_n <-  local (set tcScope TcGhost) $ getNameType n
              nt_m <-  local (set tcScope TcGhost) $ getNameType m
              case (nt_n^.val, nt_m^.val) of
                (NT_DH, NT_DH) -> return $ TSS n m
                _ -> trivialTypeOf $ args
          _ -> trivialTypeOf $ args,
    mkSimpleFunc "sign" 2 $ \args ->
        case args of
          [t1, t] | Just sk <- extractNameFromType t1 -> do
              nt <- local (set tcScope TcGhost) $  getNameType sk
              case nt^.val of
                NT_Sig t' -> do
                    assertSubtype t t'
                    l <- coveringLabel t'
                    return $ TRefined (tData l zeroLbl) $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (mkSpanned $ AELenConst "signature")
                _ -> trivialTypeOf $ args
          _ -> trivialTypeOf $ args,
    mkSimpleFunc "pkdec" 2 $ \args -> do
        case args of
          [t1, t] | Just k <- extractNameFromType t1 -> do
              nt <- local (set tcScope TcGhost) $  getNameType k
              case nt^.val of
                NT_PKE t' -> do
                    l <- coveringLabel t
                    b1 <- flowsTo (ignore def) l advLbl
                    b2 <- flowsTo (ignore def) (nameLbl k) advLbl
                    if b1 && (not b2) then do
                        -- TODO HIGH PRIORITY: fix this
                        return $ TData advLbl advLbl -- TUnion t' (tData advLbl advLbl), 
                    else do
                        let l_corr = joinLbl (nameLbl k) l
                        return $ TData l_corr l_corr,
    mkSimpleFunc "dec" 2 $ \args -> do
        debug $ pretty "Type checking decryption"
        case args of
          [t1, t] | Just k <- extractNameFromType t1 -> do
              debug $ pretty "Trying nontrivial dec"
              nt <-  local (set tcScope TcGhost) $ getNameType k
              l <- coveringLabel t
              case nt^.val of
                NT_Enc t' -> do
                    b2 <- flowsTo (ignore def) (nameLbl k) advLbl
                    if ((not b2)) then do
                        -- Honest
                        debug $ pretty "Honest dec"
                        return $ TOption t'
                    else do
                        debug $ pretty "Corrupt dec"
                        -- Corrupt
                        let l_corr = joinLbl (nameLbl k) l
                        debug $ pretty "joinLbl succeeded"
                        return $ TOption $ tData l_corr l_corr
                _ -> typeError (ignore def) $ show $  ErrWrongNameType k "encryption key" nt
          _ -> do
              l <- coveringLabelOf args
              debug $ pretty "Trivial dec"
              return $ TOption $ tData l l,
    mkSimpleFunc "vrfy" 3 $ \args ->
        case args of
          [t1, x, t] | Just k <- extractVKFromType t1 -> do
              nt <-  local (set tcScope TcGhost) $ getNameType k
              case nt^.val of
                NT_Sig t' -> do
                    debug $ pretty "Checking vrfy: " <> pretty args
                    l1 <- coveringLabel x
                    l2 <- coveringLabel t
                    b1 <- flowsTo (ignore def) l1 advLbl
                    b2 <- flowsTo (ignore def) l2 advLbl
                    b3 <- flowsTo (ignore def) (nameLbl k) advLbl
                    if (b1 && b2 && (not b3)) then return (TOption t')
                                              else do
                                               let l_corr = joinLbl (nameLbl k) (joinLbl l1 l2)
                                               return $ TOption (tData l_corr l_corr)
                _ -> typeError (ignore def) $ show $ ErrWrongNameType k "sig" nt
          _ -> do
              l <- coveringLabelOf $ args
              return $ TOption $ tData l l,
    mkSimpleFunc "mac" 2 $ \args ->
        case args of
          [t1, t] | Just k <- extractNameFromType t1 -> do
              nt <-  local (set tcScope TcGhost) $ getNameType k
              case nt^.val of
                NT_MAC t' -> do
                    assertSubtype t t'
                    l <- coveringLabel t'
                    return $ TRefined (tData l zeroLbl) $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (mkSpanned $ AELenConst "maclen")
                _ -> trivialTypeOf $ args
          _ -> trivialTypeOf $ args,
    ("mac_vrfy", (3, \ps args ->
        case (ps, args) of
          ([], [(xt1, t1), (m, mt), (xt, t)]) | Just k <- extractNameFromType t1 -> do
              nt <- local (set tcScope TcGhost) $ getNameType k
              case nt^.val of
                NT_MAC t' -> do
                    l1 <- coveringLabel mt
                    l2 <- coveringLabel t
                    b1 <- flowsTo (ignore def) l1 advLbl
                    b2 <- flowsTo (ignore def) l2 advLbl
                    b3 <- flowsTo (ignore def) (nameLbl k) advLbl
                    if (b1 && b2 && (not b3)) then
                      return $ TOption (tRefined t' $ bind (s2n ".res") (pEq (aeVar ".res") m))
                    else
                      let l_corr = joinLbl (nameLbl k) (joinLbl l1 l2) in
                      return $ TOption (tData l_corr l_corr)
          ([], _) -> do
              l <- coveringLabelOf $ map snd args
              return $ TOption $ tData l l
          _ -> typeError (ignore def) $ "params in mac_vrfy")),
    ("checknonce", (2, \ps args ->
        case (ps, args) of
          ([], [(x, t1), (y, t2)]) ->
              case ((stripRefinements t1)^.val, (stripRefinements t2)^.val) of
                (TName n, TName m) -> do
                  debug $ pretty "Checking name " <> pretty n <> pretty " against " <> pretty m
                  if n `aeq` m then return $ TRefined (mkSpanned $ TBool zeroLbl) (bind (s2n ".res") (pEq (aeVar ".res") (aeApp (topLevelPath $ "TRUE") [] [])))
                  else case (n^.val, m^.val) of
                       (BaseName (is1, is1') a, BaseName (is2, is2') b) | a == b -> do
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
    )),
    ("prf", (2, \ps args ->
        case (ps, args) of
          ([ParamStr s], [(_, t1), (a, _)]) -> do
              case (stripRefinements t1)^.val of
                TName n -> do
                    nt <-  local (set tcScope TcGhost) $ getNameType n
                    case nt^.val of
                        NT_PRF aes -> do
                          case L.find (\p -> fst p == s) aes of
                            Just (_, (ae, nt')) -> do
                                  (_, b) <- SMT.smtTypingQuery $ SMT.symCheckEqTopLevel ae a
                                  -- FL CHECK HERE 
                                  corr <- flowsTo (ignore def) (nameLbl n) advLbl
                                  if (not corr) && b then return (TName $ prfName n s) else trivialTypeOf (map snd args)
                            _ -> typeError (ignore def) $ show $ ErrUnknownPRF n s
                        _ -> typeError (ignore def) $ show $ ErrWrongNameType n "prf" nt
                _ -> typeError (ignore def) $ show $ ErrBadArgs "prf" (map snd args)
          _ -> typeError (ignore def) $ show $ ErrBadArgs "prf" (map snd args))),
    ("H", (1, \ps args ->
        case (ps, args) of
          ([ParamStr s], [(a, t)]) -> do
              ro <- view $ randomOracle
              case lookup s ro of
                Nothing -> typeError (ignore def) $ show $ pretty "Unknown RO lbl: " <> pretty s
                Just (ae, _) -> do
                  (_, b) <- SMT.smtTypingQuery $ SMT.symCheckEqTopLevel ae a
                  -- Either must be unsolvable, or flow to adv
                  uns <- unsolvability ae
                  b <- decideProp uns
                  case b of
                    Just True -> return $ TName $ roName s
                    _ -> do
                        lt <- coveringLabel t
                        flowCheck (t^.spanOf) lt advLbl
                        return $ TData advLbl advLbl
          (_, _) -> typeError (ignore def) $ "Wrong params or args to H"
    ))
    ]


initDistrs :: Map String (Int, [(AExpr, Ty)] -> Check TyX)
initDistrs = [
    ("enc", (2, \args -> do
        case args of
          [(_, t1), (x, t)] | Just k <- extractNameFromType t1 -> do
              nt <- local (set tcScope TcGhost) $  getNameType k
              case nt^.val of
                NT_Enc t' -> do
                    debug $ pretty "Checking encryption for " <> pretty k <> pretty " and " <> pretty t
                    b1 <- isSubtype t t'
                    if b1 then
                        return $ TRefined (tData zeroLbl zeroLbl) $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (aeApp (topLevelPath $ "cipherlen") [] [aeLength x])
                    else
                        trivialTypeOf $ map snd args
                _ -> typeError (ignore def) $ show $ ErrWrongNameType k "encryption key" nt
          _ -> do
              debug $ pretty "Got extremely wrong case: " <> pretty args
              trivialTypeOf $ map snd args)),
    ("pkenc", (2, \args -> do
        case args of
          [(_, t1), (x, t)] | Just k <- extractEncPKFromType t1 -> do
              nt <- local (set tcScope TcGhost) $  getNameType k
              case nt^.val of
                NT_PKE t' -> do
                    b <- isSubtype t t'
                    if (b) then
                        return $ TRefined (tData zeroLbl zeroLbl) $ bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (aeApp (topLevelPath $ "pk_cipherlen") [] [aeLength x])
                    else
                        trivialTypeOf $ map snd args
                _ -> typeError (ignore def) $ show $ ErrWrongNameType k "encryption key" nt
          _ -> trivialTypeOf $ map snd args
            ))
                        ]

interpUserFunc :: Ignore Position -> UserFunc -> Check (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX)
interpUserFunc pos (StructConstructor tv) = do
    tds <- view $ curMod . tyDefs
    case lookup tv tds of
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
                if b then return (TRefined (mkSpanned $ TConst (topLevelPath $ tv) ps) (bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (sumOfLengths (map fst xs)))) else trivialTypeOf (map snd xs)
              else trivialTypeOf (map snd xs))
      _ -> typeError pos $ "Unknown struct: " ++ show tv
interpUserFunc pos (StructProjector tv field) = do
    tds <- view $ curMod . tyDefs
    case lookup tv tds of
      Just (StructDef idf) -> do
          let (is_ar, ar) = let (xs, ys) = unsafeUnbind idf in (length xs, length ys)
          return (1, \ps args -> do
              forM_ ps checkParam
              nts <- extractStruct pos ps (show tv) idf 
              assert pos (show $ pretty "Index arity mismatch on struct constructor") $ length ps == is_ar 
              case lookup field nts of
                Just t -> do
                  b <- isSubtype (snd $ args !! 0) (mkSpanned $ TConst (topLevelPath tv) ps)
                  if b then return (t^.val) else trivialTypeOf $ map snd args
                Nothing -> typeError pos $ "Unknown struct field: " ++ field)
      _ -> typeError pos $ "Unknown struct: " ++ show tv
interpUserFunc pos (EnumConstructor tv variant) = do
    tds <- view $ curMod . tyDefs
    case lookup tv tds of
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
                Nothing -> return $ TRefined (mkSpanned $ TConst (topLevelPath tv) (ps)) (bind (s2n ".res") $ pEq (aeLength (aeVar ".res")) (aeLenConst "tag"))
                Just t -> do
                    b <- isSubtype (snd $ args !! 0) t
                    if b then return (TRefined (mkSpanned $ TConst (topLevelPath tv) (ps))
                                                          (bind (s2n ".res") $
                                                              pEq (aeLength (aeVar ".res"))
                                                                  (aeApp (topLevelPath $ "plus") [] [aeLength (fst $ args !! 0), aeLenConst "tag" ])))
                    else trivialTypeOf (map snd args))
      _ -> typeError pos $ "Unknown enum: " ++ show tv 
interpUserFunc pos (EnumTest tv variant) = do
    return $ snd $ mkSimpleFunc (variant ++ "?") 1 $ \args ->
        case args of
          [t] -> 
              case (stripRefinements t)^.val of
                TConst s _ | s == (topLevelPath tv) -> return $ TBool advLbl
                _ -> do
                    l <- coveringLabel t
                    return $ TBool l
interpUserFunc pos (UninterpUserFunc f ar) = do
    return $ (ar, withNoParams (show f) $ \args -> do
        l <- coveringLabelOf $ map snd args
        return $ TRefined (tData l l) $ bind (s2n ".res") (pEq (aeVar ".res") (aeApp (topLevelPath f) [] (map fst args))))



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
    return $ normLabel l


-- Subtype checking, assuming the types are normalized

isSubtype' t1 t2 =
    case (t1^.val, t2^.val) of
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
      (t, TDataWithLength l a) -> do
          debug $ pretty "Checking TDataWithLength with " <> pretty t1 <> pretty " <= " <> pretty t2
          b1 <- isSubtype' t1 (tData l l)
          (_, b) <- SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2
          return $ b1 && b
      (t, TData l1 l2) -> do
        l1' <- coveringLabel t1
        l2' <- tyLenLbl t1
        b1 <- flowsTo (t1^.spanOf) l1' l1
        b2 <- flowsTo (t1^.spanOf) l2' l2
        return $ b1 && b2
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
      (TRefined t _, _) -> isSubtype' t t2
      (_, TUnit) -> snd <$> (SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2)
      (TUnit,  _) -> do
        isSubtype' (tRefined (tData zeroLbl zeroLbl) $ bind (s2n "_x") (pEq (aeVar "_x") (aeApp (topLevelPath $ "UNIT") [] []))) t2
      (TBool l1, TBool l2) -> flowsTo (t1^.spanOf) l1 l2
      (TConst x ps1, TConst y ps2) | (x == y) -> do
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
      (_, TRefined t p) -> do
          b1 <- isSubtype' t1 t
          (_, b2) <- SMT.smtTypingQuery $ SMT.subTypeCheck t1 t2
          return $ b1 && b2
      (TName n, TName m) ->
          case (n^.val, m^.val) of
            (BaseName (is1, is1') a, BaseName (is2, is2') b) | a == b -> do
              debug $ pretty "Equality query on indices " <> pretty (is1 ++ is1') <> pretty " and " <> pretty (is2 ++ is2')
              let p =  foldr pAnd pTrue $ map (\(i, j) -> mkSpanned $ PEqIdx i j) $ zip (is1 ++ is1') (is2 ++ is2')
              (_, b) <- SMT.smtTypingQuery $ SMT.symAssert p
              return b
            _ -> return False
      _ -> return False

-- We check t1 <: t2  by first normalizing both
isSubtype :: Ty -> Ty -> Check Bool
isSubtype t1 t2 = do
    debug $ pretty (unignore $ t1^.spanOf) <> pretty (unignore $ t2^.spanOf) <> pretty "Checking subtype of " <> pretty t1 <> pretty " and " <> pretty t2
    t1' <- normalizeTy t1
    t2' <- normalizeTy t2
    isSubtype' t1' t2'

assertSubtype :: Ty -> Ty -> Check ()
assertSubtype t1 t2 = do
    tyc <- view tyContext
    debug $ pretty "Asserting subtype " <> pretty t1 <> pretty " <= " <> pretty t2 <> pretty "Under context: " <> prettyTyContext tyc
    t1' <- normalizeTy t1
    t2' <- normalizeTy t2
    b <- isSubtype' t1' t2'
    assert (t1^.spanOf) (show $ ErrCannotProveSubtype t1' t2') b

typeProtectsLabel' :: Label -> Ty -> Check ()
typeProtectsLabel' l t0 =
    case t0^.val of
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
typeProtectsLabel l t = do
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
          (_, DefSpec abs2 _ _) <- unbind isdp
          assert pos ("Duplicate abstract def: " ++ n) $ not (unignore abs1)
          assert pos ("Def already defined: " ++ n) $ unignore abs2
          assert pos ("Concrete def mismatch with abstract def: " ++ n) $ isdp `aeq` isdp'
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
            forM_ nls (checkLocality (nt^.spanOf))
            checkNameType nt
    local (over (curMod . nameEnv) $ insert n (bind (is1, is2) (Just (nt, nls)))) $ k

sumOfLengths :: [AExpr] -> AExpr
sumOfLengths [] = aeApp (topLevelPath $ "zero") [] []
sumOfLengths (x:xs) = aeApp (topLevelPath $ "plus") [] [aeLength x, sumOfLengths xs]

checkDecl :: Decl -> Check a -> Check a
checkDecl d cont = 
    case d^.val of
      (DeclLocality n i) -> local (over (curMod . localities) $ insert n i) $ cont
      DeclInclude _ -> error "Include found during type inference"
      DeclName n o -> do
        ((is1, is2), ntnlsOpt) <- unbind o
        case ntnlsOpt of
          Nothing ->  local (over (curMod . nameEnv) $ insert n (bind (is1, is2) Nothing)) $ cont
          Just (nt, nls) -> addNameDef n (is1, is2) (nt, nls) $ cont
      DeclModule n xds' -> do
          (x, ds') <- unbind xds'
          m' <- local (over curModules $ insert (Just x) emptyModDef) $ do
              checkDeclsWithCont ds' $ view curMod
          local (over (curMod . modules) $ insert n (bind x m')) $ cont
      DeclDefHeader n isl -> do
          ((is1, is2), l) <- unbind isl
          local (over inScopeIndices $ mappend $ map (\i -> (i, IdxSession)) is1) $ do
              local (over inScopeIndices $ mappend $ map (\i -> (i, IdxPId)) is2) $ do
                  checkLocality (d^.spanOf) l
          let df = DefHeader isl 
          addDef (d^.spanOf) n df $ cont
      DeclDef n o1 -> do
          ((is1, is2), (l, o2)) <- unbind o1
          (xs, (opreReq, tyAnn, bdy)) <- unbind o2
          let preReq = case opreReq of
                         Nothing -> pTrue
                         Just p -> p
          is_abs <- local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxSession)) is1) $ do
              local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxPId)) is2) $ do
                  checkLocality (d^.spanOf) l
                  forM_ xs $ \(x, t) -> checkTy $ unembed t
                  withVars (map (\(x, t) -> (x, (ignore $ show x, unembed t))) xs) $ do
                      checkProp preReq
                      checkTy tyAnn
                      let happenedProp = pHappened (topLevelPath n) (map mkIVar is1, map mkIVar is2) (map aeVar' $ map fst xs)
                      x <- freshVar
                      case bdy of
                        Nothing -> return $ ignore True
                        Just bdy' -> do
                          bdy'' <- ANF.anf bdy'
                          local (set tcScope $ TcDef l) $
                              withVars [(s2n x, (ignore x, mkSpanned $ TRefined tUnit (bind (s2n ".req") (pAnd preReq happenedProp))))] $ do
                              t <- checkExpr (Just tyAnn) bdy''
                              -- let p1 = atomicCaseSplits t
                              -- let p2 = atomicCaseSplits tyAnn
                              -- let ps = map _unAlphaOrd $ S.toList $ p1 `S.union` p2
                              -- withAllSplits ps $ assertSubtype t tyAnn
                              return $ ignore False
          let df = Def $ bind (is1, is2) $ DefSpec is_abs l (bind xs (preReq, tyAnn))
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
          checkLocality (d^.spanOf) loc
          checkTy t
          local (over (curMod . tableEnv) $ insert n (t, loc)) cont
      (DeclDetFunc f opts ar) -> do
        dfs <- view detFuncs
        assert (d^.spanOf) (show $ pretty f <+> pretty "already defined") $ not $ member f dfs
        local (over (curMod . userFuncs) $ insert f (UninterpUserFunc f ar)) $ 
            cont
      (DeclRandOrcl s (ae, nt)) -> do
        -- assert (d^.spanOf) (show $ pretty "TODO: params") $ length ps == 0
        _ <- inferAExpr ae
        checkNameType nt
        checkROName nt
        checkROUnique ae
        ro <- view $ randomOracle
        assert (d^.spanOf) (show $ pretty "Duplicate RO lbl: " <> pretty s) $ not $ member s ro
        local (over (randomOracle) $ insert s (ae, nt)) cont 

-- TODO: move up
--checkDecl :: Decl -> Check () -> Check ()
--checkDecl dcl k =
--    case dcl^.val of
--      (DeclInclude fn) -> error "Include found during type inference"
--      (DeclName n o) -> do
--        ((is1, is2), ntnlsOpt) <- unbind o
--        case ntnlsOpt of
--          Nothing ->  local (over (curMod . nameEnv) $ insert n (bind (is1, is2) Nothing)) $ k
--          Just (nt, nls) -> addNameDef n (is1, is2) (nt, nls) k
--      DeclDef n o1 -> do
--          ((is1, is2), (l, o2)) <- unbind o1
--          (xs, (opreReq, tyAnn, bdy)) <- unbind o2
--          let preReq = case opreReq of
--                         Nothing -> pTrue
--                         Just p -> p
--          is_abs <- local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxSession)) is1) $ do
--              local (over (inScopeIndices) $ mappend $ map (\i -> (i, IdxPId)) is2) $ do
--                  checkLocality (dcl^.spanOf) l
--                  forM_ xs $ \(x, t) -> checkTy $ unembed t
--                  withVars (map (\(x, t) -> (x, (ignore $ show x, unembed t))) xs) $ do
--                      checkProp preReq
--                      checkTy tyAnn
--                      let happenedProp = pHappened (topLevelPath n) (map mkIVar is1, map mkIVar is2) (map aeVar' $ map fst xs)
--                      x <- freshVar
--                      case bdy of
--                        Nothing -> return $ DefAbstract
--                        Just bdy' -> do
--                          bdy'' <- ANF.anf bdy'
--                          local (set tcScope $ Def l) $
--                              withVars [(s2n x, (ignore x, mkSpanned $ TRefined tUnit (bind (s2n ".req") (pAnd preReq happenedProp))))] $ do
--                              t <- checkExpr (Just tyAnn) bdy''
--                              -- let p1 = atomicCaseSplits t
--                              -- let p2 = atomicCaseSplits tyAnn
--                              -- let ps = map _unAlphaOrd $ S.toList $ p1 `S.union` p2
--                              -- withAllSplits ps $ assertSubtype t tyAnn
--                              return $ DefConcrete
--          let fdef = bind (is1, is2) $ FuncDef l (bind xs (preReq, tyAnn))
--          dfs <- view $ curMod . defs
--          case lookup n dfs of
--            Nothing -> local (over (curMod . defs) $ insert n (is_abs, fdef)) k
--            Just (DefConcrete, _) -> typeError (dcl^.spanOf) $ show $ pretty "Duplicate definition: " <> pretty n
--            Just (DefAbstract, fd') -> do -- Do the subtyping
--                assert (ignore def) (show $ pretty "Duplicate abstract def: " <> pretty n) $ is_abs == DefConcrete
--                assert (ignore def) (show $ pretty "Concrete def mismatch with abstract def: " <> pretty n) $
--                    fdef
--                    `aeq`
--                    fd'
--                local (over (curMod . defs) $ insert n (is_abs, fdef)) k
--      (DeclModule s xds) -> do
--          (x, ds) <- unbind xds
--          return ()


checkROName :: NameType -> Check ()
checkROName nt =  
    case nt^.val of
      NT_Nonce -> return ()
      NT_Enc _ -> return ()
      NT_MAC _ -> return ()
      _ -> typeError (nt^.spanOf) $ "Bad RO Name: " ++ show (pretty nt)

atomicProps :: Prop -> S.Set (AlphaOrd Prop)
atomicProps p =
    case p^.val of
      PAnd p1 p2 -> S.union (atomicProps p1) (atomicProps p2)
      POr p1 p2 -> S.union (atomicProps p1) (atomicProps p2)
      PImpl p1 p2 -> S.union (atomicProps p1) (atomicProps p2)
      PNot p -> atomicProps p
      PTrue -> S.empty
      PFalse -> S.empty
      PEq _ _-> S.singleton (AlphaOrd p)
      PEqIdx _ _ -> S.singleton (AlphaOrd p)
      PFlow _ _ -> S.singleton (AlphaOrd p)
      PHappened _ _ _ -> S.singleton (AlphaOrd p)

atomicCaseSplits :: Ty -> S.Set (AlphaOrd Prop)
atomicCaseSplits t =
    case t^.val of
      TCase p t1 t2 -> atomicProps p `S.union` (atomicCaseSplits t1 `S.union` atomicCaseSplits t2)
      TOption t -> atomicCaseSplits t
      TRefined t _ -> atomicCaseSplits t
      TUnion t1 t2 -> atomicCaseSplits t1 `S.union` atomicCaseSplits t2
      _ -> S.empty

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


checkROUnique :: AExpr -> Check ()
checkROUnique e = do
    ro_vals <- view $ randomOracle
    (_, b) <- SMT.smtTypingQuery $ SMT.symROUnique (map fst $ map snd $ ro_vals) e
    assert (e^.spanOf) "RO uniqueness check failed" b
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
      NT_PKE t -> do
          checkTy t
          checkTyPubLen t
      NT_MAC t -> checkTy t

checkParam :: FuncParam -> Check ()
checkParam (ParamAExpr a) = do
    _ <- inferAExpr a
    return ()
checkParam (ParamStr s) = return ()
checkParam (ParamLbl l) =  checkLabel l
checkParam (ParamTy t) =  checkTy t
checkParam (ParamIdx i) = local (set tcScope TcGhost) $ checkIdx i

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
            TCase p _ _ -> typeError (t^.spanOf) $ show $ pretty "Inconclusive: " <> pretty p
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
checkTyPubLen t0 = do
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
flowCheck sp l1 l2 = do
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


checkLocality :: Ignore Position -> Locality -> Check ()
checkLocality pos pth@(Locality (PRes (PDot p s)) xs) = do
    md <- getModule pos p
    case lookup s (md^.localities) of 
          Nothing -> typeError pos $ show $ pretty "Unknown locality: " <> pretty pth
          Just ar -> do
              assert pos (show $ pretty "Wrong arity for locality " <> pretty pth) $ ar == length xs
              forM_ xs $ \i -> do
                  it <- inferIdx i
                  assert pos (show $ pretty "Index should be party ID: " <> pretty i) $ it == IdxPId
checkLocality pos pth = error $ "Bad path: " ++ show pth


checkEndpoint :: Ignore Position -> Endpoint -> Check ()
checkEndpoint pos (Endpoint x) = do
    s <- view $ curMod . endpointContext
    assert pos (show $ pretty "Unknown endpoint: " <> pretty x) $ elem x s
checkEndpoint pos (EndpointLocality l) = do
    checkLocality pos l

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
      (EInput xsk) -> do
          ((x, s), k) <- unbind xsk
          withVars [(x, (ignore $ show x, tData advLbl advLbl))] $ local (over (curMod . endpointContext) (s :)) $ checkExpr ot k
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
          ms <- view curModules
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
      (ESamp d args) -> do
          ts <- mapM inferAExpr args
          ts <- mapM normalizeTy ts
          dE <- view distrs
          case lookup d dE of
            Just (ar, k) -> do
                assert (e^.spanOf) (show $ pretty "Wrong arity for " <> pretty d) $ length ts == ar
                getOutTy ot =<< mkSpanned <$> (k $ zip args ts)
            Nothing -> typeError (e^.spanOf) $ show (ErrUnknownDistr d)
      (ETLookup pth@(PRes (PDot p n)) a) -> do
          md <- getModule (e^.spanOf) p
          case lookup n (md^.tableEnv) of 
            Nothing -> typeError (e^.spanOf) $ show $ pretty (unignore $ a^.spanOf) <+> pretty "Unknown table: " <> pretty n
            Just (t, loc) -> do
                tc <- view tcScope
                ta <- inferAExpr a
                assertSubtype ta (tData advLbl advLbl)
                case tc of
                  TcDef curr_loc -> do
                      assert (e^.spanOf) (show $ pretty "Wrong locality for table: got" <> pretty curr_loc <+> pretty "but expected" <+> pretty loc) $ curr_loc `aeq` loc
                      getOutTy ot $ mkSpanned $ TOption t
                  _ -> typeError (e^.spanOf) $ "Weird case: should be in a def"
      (ETWrite pth@(PRes (PDot p n)) a1 a2) -> do
          md <- getModule (e^.spanOf) p
          case lookup n (md^.tableEnv) of 
            Nothing -> typeError (e^.spanOf) $ show $  pretty (unignore $ e^.spanOf) <+> pretty "Unknown table: " <> pretty n
            Just (t, loc) -> do
                tc <- view tcScope
                case tc of
                  TcDef curr_loc -> do
                      assert (e^.spanOf) (show $ pretty "Wrong locality for table: got" <> pretty curr_loc <+> pretty "but expected" <+> pretty loc) $ curr_loc `aeq` loc
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
                assert (e^.spanOf) (show $ pretty "Wrong locality for function call") $ fl `aeq` curr_locality
                (xts, (pr, rt)) <- unbind o
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
      (ECorrCase n e) -> do
          _ <- local (set tcScope TcGhost) $ getNameTypeOpt n
          x <- freshVar
          t1 <- withVars [(s2n x, (ignore x, tLemma (pFlow (nameLbl n) advLbl)))] $ do
              (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ mkSpanned PFalse
              if b then getOutTy ot tAdmit else checkExpr ot e
          t2 <- withVars [(s2n x, (ignore x, tLemma (pNot $ pFlow (nameLbl n) advLbl)))] $ do
              (_, b) <- SMT.smtTypingQuery $ SMT.symAssert $ mkSpanned PFalse
              if b then getOutTy ot tAdmit else checkExpr ot e 
          return $ mkSpanned $ TCase (mkSpanned $ PFlow (nameLbl n) advLbl) t1 t2
      (ECase a cases) -> do
          debug $ pretty "Typing checking case: " <> pretty (unignore $ e^.spanOf)
          t <- inferAExpr a
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
          flowCheck (t'^.spanOf) l advLbl
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

unsolvability :: AExpr -> Check Prop
unsolvability ae = local (set tcScope TcGhost) $ do
    case ae^.val of
      AEApp f [] [x, y] | f == (topLevelPath $ "dh_combine")-> do
          t1 <- inferAExpr x
          t2 <- inferAExpr y
          case (t1^.val, t2^.val) of
            (TDH_PK n, TName m) -> return $ pAnd (pNot $ pFlow (nameLbl n) advLbl) (pNot $ pFlow (nameLbl m) advLbl)
            _ -> return pFalse
      AEApp f [] xs -> do
          uf <- getUserFunc (ae^.spanOf) f
          case uf of
            Just (StructConstructor _) -> do -- f is a constructor of a struct; derivability is the and
                ps <- mapM unsolvability xs
                return $ foldr pOr pFalse ps
            _ -> return pFalse
      _ -> do
          t <- inferAExpr ae
          case t^.val of
            TName n -> return $ pNot $ pFlow (nameLbl n) advLbl
            _ -> return pFalse

---- Entry point ----

typeCheckDecls :: Flags -> [Decl] -> IO (Either Env ())
typeCheckDecls f ds = do
    e <- emptyEnv f
    r <- PR.runResolve f $ PR.resolveDecls ds
    case r of
      Left () -> return $ Left e
      Right ds' -> do
          runExceptT $ runReaderT (unCheck $ checkDecls ds') e


