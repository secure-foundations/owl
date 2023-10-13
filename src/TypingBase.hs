{-# LANGUAGE TemplateHaskell #-} 
{-# LANGUAGE GeneralizedNewtypeDeriving #-} 
{-# LANGUAGE FlexibleInstances #-} 
{-# LANGUAGE MultiParamTypeClasses #-} 
{-# LANGUAGE UndecidableInstances #-} 
{-# LANGUAGE FlexibleContexts #-} 
{-# LANGUAGE DataKinds #-} 
{-# LANGUAGE RankNTypes #-} 
{-# LANGUAGE DeriveGeneric #-}
module TypingBase where
import AST
import qualified Data.Set as S
import Data.Maybe
import Data.Serialize
import Data.IORef
import System.Directory
import Control.Monad
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.ByteString as BS
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Cont
import CmdArgs
import System.FilePath
import Prettyprinter
import Prettyprinter.Render.Terminal
import Pretty
import Control.Lens
import Control.Lens.At
import Error.Diagnose
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Unsafe
import System.FilePath ((</>))
import System.IO
import qualified Parse as P


member :: Eq a => a -> [(a, b)] -> Bool
member k xs = elem k $ map fst xs

insert :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
insert k v xs = (k, v) : (filter (\p -> k /= (fst p)) xs)

insertMany :: Eq a => [(a, b)] -> [(a, b)] -> [(a, b)]
insertMany kvs xs = kvs ++ filter (\p -> not (fst p `elem` map fst kvs)) xs 

data TcScope = 
      TcGhost 
      | TcDef Locality
      deriving (Show, Generic, Typeable)

instance Alpha TcScope

instance OwlPretty TcScope where
    owlpretty TcGhost = owlpretty "ghost"
    owlpretty (TcDef l) = owlpretty "def" <> tupled [owlpretty l]


instance OwlPretty IdxType where
    owlpretty IdxSession = owlpretty "IdxSession"
    owlpretty IdxPId = owlpretty "IdxPId"
    owlpretty IdxGhost = owlpretty "IdxGhost"

data Def = 
    DefHeader (Bind ([IdxVar], [IdxVar]) Locality)-- All we we know is the arity
    | Def (Bind ([IdxVar], [IdxVar]) DefSpec)
    deriving (Show, Generic, Typeable)

instance Alpha Def
instance Subst Idx Def
instance Subst ResolvedPath Def

data DefSpec = DefSpec {
    _isAbstract :: Ignore Bool, 
    _defLocality :: Locality,
    _preReq_retTy_body :: Bind [(DataVar, Embed Ty)] (Prop, Ty, Maybe Expr)
}
    deriving (Show, Generic, Typeable)

instance Alpha DefSpec
instance Subst Idx DefSpec
instance Subst ResolvedPath DefSpec

type Map a b = [(a, b)]


data UserFunc =
    StructConstructor TyVar 
      | StructProjector TyVar String  
      | EnumConstructor TyVar String
      | EnumTest TyVar String
      | UninterpUserFunc String Int
      | FunDef (Bind (([IdxVar], [IdxVar]), [DataVar]) AExpr)
    deriving (Show, Generic, Typeable)

instance Alpha UserFunc
instance Subst ResolvedPath UserFunc

data ModDef = 
    MBody (Bind (Name ResolvedPath) ModBody)
    | MAlias ResolvedPath -- Only aliases for modules, not functors
    | MFun String ModDef (Bind (Name ResolvedPath) ModDef)
    deriving (Show, Generic, Typeable)

instance Alpha ModDef
instance Subst ResolvedPath ModDef

data NameDef = 
    BaseDef (NameType, [Locality])
      | AbstractName
      | RODef ROStrictness (Bind [DataVar] (AExpr, Prop, [NameType]))
      deriving (Show, Generic, Typeable)

instance Alpha NameDef
instance Subst ResolvedPath NameDef
instance Subst Idx ROStrictness
instance Subst Idx NameDef

data ModBody = ModBody { 
    _isModuleType :: IsModuleType,
    _localities :: Map String (Either Int ResolvedPath), -- left is arity; right is if it's a synonym
    _defs :: Map String Def, 
    _tableEnv :: Map String (Ty, Locality),
    _flowAxioms :: [(Label, Label)],
    _predicates :: Map String (Bind ([IdxVar], [DataVar]) Prop),
    _advCorrConstraints :: [Bind ([IdxVar], [DataVar]) (Label, Label)],
    _tyDefs :: Map TyVar TyDef,
    _userFuncs :: Map String UserFunc,
    _nameDefs :: Map String (Bind ([IdxVar], [IdxVar]) NameDef), 
    _ctrEnv :: Map String (Bind ([IdxVar], [IdxVar]) Locality),
    _modules :: Map String ModDef
}
    deriving (Show, Generic, Typeable)

instance Alpha ModBody
instance Subst ResolvedPath ModBody

data Env = Env { 
    _envFlags :: Flags,
    _detFuncs :: Map String (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX), 
    _tyContext :: Map DataVar (Ignore String, (Maybe AExpr), Ty),
    _tcScope :: TcScope,
    _endpointContext :: [EndpointVar],
    _inScopeIndices ::  Map IdxVar IdxType,
    _openModules :: Map (Maybe (Name ResolvedPath)) ModBody, 
    _modContext :: Map (Name ResolvedPath) ModDef,
    _interpUserFuncs :: ResolvedPath -> ModBody -> UserFunc -> Check (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX),
    -- in scope atomic localities, eg "alice", "bob"; localities :: S.Set String -- ok
    _freshCtr :: IORef Integer,
    _smtCache :: IORef (M.Map Int Bool),
    _z3Options :: M.Map String String, 
    _z3Results :: IORef (Map String P.Z3Result),
    _typeCheckLogDepth :: IORef Int,
    _debugLogDepth :: IORef Int,
    _typeErrorHook :: (forall a. String -> Check a),
    _curDef :: Maybe String,
    _inTypeError :: Bool,
    _curSpan :: Position
}


data TyDef = 
    EnumDef (Bind [IdxVar] [(String, Maybe Ty)])
      | StructDef (Bind [IdxVar] [(String, Ty)])
      | TyAbbrev Ty
      | TyAbstract -- Public length
    deriving (Show, Generic, Typeable)

instance Alpha TyDef
instance Subst Idx TyDef
instance Subst ResolvedPath TyDef

data TypeError =
    ErrWrongNameType NameExp String NameType
      | ErrBadArgs String [Ty] 
      | ErrWrongCases String AExpr (Map String (Maybe Ty)) (Map String (Either Expr (Ignore String, Bind DataVar Expr)))
      | ErrUnknownName Path
      | ErrUnknownRO ResolvedPath
      | ErrUnknownPRF NameExp String
      | ErrAssertionFailed (Maybe String) Prop
      | ErrDuplicateVarName DataVar
      | ErrUnknownFunc (Path)
      | ErrFlowCheck Label Label
      | ErrUnknownVar  DataVar
      | ErrUnknownType String
      | ErrLenAmbiguous Ty
      | ErrWrongLocality NameExp Locality (S.Set Locality)
      | ErrCannotProveSubtype Ty Ty
      | ErrNameStillAbstract String

instance OwlPretty (TypeError) where
    owlpretty (ErrWrongNameType n s nt) = 
        owlpretty "Wrong name type for " <> owlpretty n <> owlpretty ": expected " <> owlpretty s <> owlpretty ", got " <> owlpretty nt
    owlpretty (ErrBadArgs s ts) = 
        owlpretty "Bad argument types for " <> owlpretty s <> owlpretty ": got " <> owlpretty ts
    owlpretty (ErrUnknownRO s) = 
        owlpretty "Unknown random oracle value: " <> owlpretty (show s)
    owlpretty (ErrUnknownPRF n s) = 
        owlpretty "Unknown prf value for " <> owlpretty n <> owlpretty ": " <> owlpretty s
    owlpretty (ErrDuplicateVarName s) = 
        owlpretty "Duplicate variable name: " <> owlpretty s
    owlpretty (ErrWrongCases s a expected actual) = 
        owlpretty "Wrong cases for " <> owlpretty s <> owlpretty " with "  <> owlpretty a  <> owlpretty " expected " <> owlpretty (map fst expected) <> owlpretty " but got " <> owlpretty (map fst actual)
    owlpretty (ErrAssertionFailed fn p) =
        owlpretty "Assertion failed: " <> owlpretty p <> owlpretty " from " <> owlpretty fn
    owlpretty (ErrUnknownName s) =  
        owlpretty "Unknown name: " <> owlpretty s
    owlpretty (ErrUnknownFunc s) =  
        owlpretty "Unknown func: " <> owlpretty s
    owlpretty (ErrUnknownVar s) =  
        owlpretty "Unknown variable: " <> owlpretty s
    owlpretty (ErrUnknownType s) =  
        owlpretty "Unknown type name: " <> owlpretty s
    owlpretty (ErrFlowCheck l1 l2) =  
        owlpretty "Label " <> owlpretty l1 <> owlpretty " does not flow to " <> owlpretty l2
    owlpretty (ErrLenAmbiguous t) = 
        owlpretty "Type " <> owlpretty t <> owlpretty " has an ambiguous length"
    owlpretty (ErrCannotProveSubtype t1 t2) = 
        owlpretty "Cannot prove type " <> owlpretty t1 <> owlpretty " is a subtype of " <> owlpretty t2
    owlpretty (ErrWrongLocality n l ls) = 
        owlpretty "Locality of name " <> owlpretty n <> owlpretty " is not available to locality " <> owlpretty l
    owlpretty (ErrNameStillAbstract n) =
        owlpretty "Name" <+> owlpretty n <+> owlpretty "is abstract but needs to be concrete here"

instance Show TypeError where
    show = show . owlpretty

newtype Check a = Check { unCheck :: ReaderT Env (ExceptT Env IO) a }
    deriving (Functor, Applicative, Monad, MonadReader Env, MonadIO)


makeLenses ''DefSpec

makeLenses ''Env

makeLenses ''ModBody

modDefKind :: ModDef -> Check IsModuleType
modDefKind (MBody xd) =
    let (_, d) = unsafeUnbind xd in return $ _isModuleType d
modDefKind (MFun _ _ xd) = 
    let (_, d) = unsafeUnbind xd in modDefKind d
modDefKind (MAlias p) = do
    md <- getModDef p
    modDefKind md


makeModDefConcrete :: ModDef -> Check ModDef
makeModDefConcrete (MBody xd) = do
    (x, d) <- unbind xd
    return $ MBody $ bind x $ set isModuleType ModConcrete d
makeModDefConcrete (MFun s t xk) = do
    (x, k) <- unbind xk
    k' <- makeModDefConcrete k
    return $ MFun s t $ bind x k'
makeModDefConcrete (MAlias p) = do
    md <- getModDef p
    makeModDefConcrete md

instance Fresh Check where
    fresh (Fn s _) = do
        r <- view freshCtr
        n <- liftIO $ readIORef r
        liftIO $ writeIORef r (n + 1)
        return $ (Fn s n)
    fresh nm@(Bn {}) = return nm

instance MonadFail Check where
    fail s = error s

removeAnfVars :: Map DataVar (Ignore String, (Maybe AExpr), Ty) -> Map DataVar (Ignore String, (Maybe AExpr), Ty)
removeAnfVars ctxt = L.foldl' g [] ctxt where
    g acc (v, (s, anf, t)) = case anf of
        Nothing -> acc ++ [(v, (s, anf, hideAnfVarsInTy ctxt t))]
        Just _ -> acc

hideAnfVarsInTy :: Map DataVar (Ignore String, (Maybe AExpr), Ty) -> Ty -> Ty
hideAnfVarsInTy ctxt t = L.foldl' substAnfVar t ctxt where
    substAnfVar :: Ty -> (DataVar, (Ignore String, (Maybe AExpr), Ty)) -> Ty
    substAnfVar ty (v, (_, anf, _)) = do
        case anf of
            Nothing -> ty
            Just anfOrig -> subst v anfOrig ty

typeError x = do
    th <- view typeErrorHook
    th x

writeSMTCache :: Check ()
writeSMTCache = do
    cacheref <- view smtCache
    cache <- liftIO $ readIORef cacheref
    filepath <- view $ envFlags . fFilePath
    let hintsFile = filepath ++ ".smtcache"
    liftIO $ BS.writeFile hintsFile $ encode cache

loadSMTCache :: Check ()
loadSMTCache = do
    filepath <- view $ envFlags . fFilePath
    let hintsFile = filepath ++ ".smtcache"
    b <- liftIO $ doesFileExist hintsFile
    when b $ do
        clean <- view $ envFlags . fCleanCache
        if clean then liftIO $ removeFile hintsFile
        else do
            cache <- liftIO $ BS.readFile hintsFile
            cacheref <- view smtCache
            case decode cache of
              Left s -> do
                  TypingBase.warn $ "Could not decode SMT cache: " ++ s ++ ", deleting file"
                  liftIO $ removeFile hintsFile
              Right c -> do
                  liftIO $ putStrLn $ "Found smtcache file: " ++ hintsFile
                  liftIO $ writeIORef cacheref $ c


warn :: String -> Check ()
warn msg = liftIO $ putStrLn $ "Warning: " ++ msg

--instance (Monad m, MonadIO m, MonadReader Env m) => Fresh m where

freshVar :: Check String
freshVar = do
    r <- view freshCtr
    i <- liftIO $ readIORef r
    liftIO $ writeIORef r (i + 1)
    return $ ".x" ++ show i

freshIdx :: Check String
freshIdx = do
    r <- view freshCtr
    i <- liftIO $ readIORef r
    liftIO $ writeIORef r (i + 1)
    return $ ".i" ++ show i

freshLbl :: Check String
freshLbl = do
    r <- view freshCtr
    i <- liftIO $ readIORef r
    liftIO $ writeIORef r (i + 1)
    return $ ".l" ++ show i

-- Convenience functions for adding to the environment 


joinLbl :: Label -> Label -> Label
joinLbl l1 l2 = 
    if (l1^.val) `aeq` LZero then l2 else
    if (l2^.val) `aeq` LZero then l1 else 
    mkSpanned $ LJoin l1 l2


addVars :: [(DataVar, (Ignore String, (Maybe AExpr), Ty))] -> Map DataVar (Ignore String, (Maybe AExpr), Ty) -> Map DataVar (Ignore String, (Maybe AExpr), Ty)
addVars xs g = g ++ xs 
    
assert :: String -> Bool -> Check ()
assert m b = do
    if b then return () else typeError m 

laxAssertion :: Check () -> Check ()
laxAssertion k = do
    b1 <- view $ envFlags . fLax
    onlyCheck <- view $ envFlags . fOnlyCheck
    cd <- view curDef
    let b2 = case onlyCheck of
               Just s -> (cd /= Just s) -- Only lax if onlyCheck is Just s, and we are not in method s
               Nothing -> False
    if b1 || b2 then return () else k

-- withVars xs k = add xs to the typing environment, continue as k with extended
-- envrionment

withVars :: [(DataVar, (Ignore String, (Maybe AExpr), Ty))] -> Check a -> Check a
withVars assocs k = do
    tyC <- view tyContext
    forM_ assocs $ \(x, _) -> 
        assert (show $ ErrDuplicateVarName x) $ not $ elem x $ map fst tyC
    local (over tyContext $ addVars assocs) k


unsafeHead :: Lens' [a] a
unsafeHead = lens gt st
    where
        gt = head
        st (_:xs) a = a:xs

unsafeLookup :: (Eq a, Show a) => a -> Lens' (Map a b) b
unsafeLookup x = lens gt st
    where
        gt a = case lookup x a of
                 Just v -> v
                 Nothing -> error $ "INTERNAL ERROR: Unknown key: " ++ show x
        st m b = insert x b m

curMod :: Lens' Env ModBody
curMod = openModules . unsafeHead . _2

curModName :: Check ResolvedPath
curModName = do
    (k, _) <- head <$> view openModules
    case k of
      Nothing -> return PTop
      Just pv -> return $ PPathVar OpenPathVar pv

withSpan :: (Ignore Position) -> Check a -> Check a
withSpan x k = do
        res <- local (set curSpan (unignore x)) k
        return res

traceFn :: (MonadIO m, MonadReader Env m) => String -> m a -> m a
traceFn ann k = do
    r <- view $ debugLogDepth
    b <- view $ envFlags . fDebug
    case b of
      Just fname -> do
          n <- liftIO $ readIORef r
          -- liftIO $ appendFile fname $ replicate (n) ' ' ++ ann ++ "\n"
          liftIO $ appendFile fname $ ann ++ "\n"
          liftIO $ modifyIORef r (+1)
          res <- k 
          liftIO $ modifyIORef r (\x -> x - 1)
          return res
      Nothing -> k

inferIdx :: Idx -> Check IdxType
inferIdx (IVar pos i) = withSpan pos $ do
    m <- view $ inScopeIndices
    tc <- view tcScope
    case lookup i m of
      Just t -> 
          case (tc, t) of
            (TcDef _, IdxGhost) ->  
                typeError $ "Index should be nonghost: " ++ show (owlpretty i) 
            _ -> return t
      Nothing -> typeError $ "Unknown index: " ++ show (owlpretty i)

checkIdx :: Idx -> Check ()
checkIdx i = do
    _ <- inferIdx i
    return ()

checkIdxSession :: Idx -> Check ()
checkIdxSession i@(IVar pos _) = do
    it <- inferIdx i
    tc <- view tcScope
    case tc of
       TcGhost -> assert (show $ owlpretty "Wrong index type: " <> owlpretty i <> owlpretty ", got " <> owlpretty it <+> owlpretty " expected Ghost or Session ID") $ it /= IdxPId
       TcDef _ ->  assert (show $ owlpretty "Wrong index type: " <> owlpretty i <> owlpretty ", got " <> owlpretty it <+> owlpretty " expected Session ID") $ it == IdxSession

checkIdxPId :: Idx -> Check ()
checkIdxPId i@(IVar pos _) = do
    it <- inferIdx i
    tc <- view tcScope
    case tc of
       TcGhost -> assert (show $ owlpretty "Wrong index type: " <> owlpretty i <> owlpretty ", got " <> owlpretty it <+> owlpretty " expected Ghost or PId") $ it /= IdxSession
       TcDef _ -> assert (show $ owlpretty "Wrong index type: " <> owlpretty i <> owlpretty ", got " <> owlpretty it <+> owlpretty "expected PId") $ it == IdxPId

openModule :: ResolvedPath -> Check ModBody
openModule rp = do
    mb <- go rp
    tc <- view tcScope
    case tc of
      TcDef _ -> assert ("Module must be concrete: " ++ show rp) $ (mb^.isModuleType) == ModConcrete 
      _ -> return ()
    return mb
    where
        go :: ResolvedPath -> Check ModBody
        go PTop = view $ openModules . unsafeLookup Nothing
        go (PPathVar OpenPathVar v) = view $ openModules . unsafeLookup (Just v)
        go p0@(PPathVar (ClosedPathVar _) v) = do
            mc <- view modContext
            case lookup v mc of
              Just (MBody xmb) -> do
                  (x, mb) <- unbind xmb
                  return $ subst x p0 mb 
              Just (MAlias p) -> go p
              Just (MFun _ _ _) -> typeError $ show p0 ++ " is not a module"
              Nothing -> typeError $ "Unknown module or functor (functor argument, openModule): " ++ show p0
        go p0@(PDot p' s) = do
            md <- go p'
            case lookup s (md^.modules) of
              Just (MAlias p) -> go p
              Just (MBody xmb) -> do
                  (x, mb) <- unbind xmb
                  return $ subst x p0 mb
              Just (MFun _ _ _) -> typeError $ show p0 ++ " is not a module"
              Nothing -> typeError $ "Unknown module: " ++ show p0

stripRefinements :: Ty -> Ty
stripRefinements t =
    case t^.val of
      TRefined t _ _ -> stripRefinements t
      _ -> t

getModDef :: ResolvedPath -> Check ModDef
getModDef rp = do
    go rp
    where
        go :: ResolvedPath -> Check ModDef
        go PTop = typeError $ "Got top for getModDef"
        go (PPathVar OpenPathVar v) = typeError $ "Got opened module var for getModDef"
        go (PPathVar (ClosedPathVar _) v) = do
            mc <- view modContext
            case lookup v mc of
              Just b -> return b
              Nothing -> typeError $ "Unknown module or functor (functor argument, getModDef): " ++ show rp
        go p0@(PDot p' s) = do
            md <- openModule p'
            case lookup s (md^.modules) of
              Just b -> return b
              Nothing -> typeError $ "Unknown module or functor: " ++ show rp

checkCounterIsLocal :: Path -> ([Idx], [Idx]) -> Check ()
checkCounterIsLocal p0@(PRes (PDot p s)) (vs1, vs2) = do
    md <- openModule p
    case lookup s (md^.ctrEnv) of
      Just r -> do
          forM_ vs1 checkIdxSession
          forM_ vs2 checkIdxPId
          ((is1, is2), l) <- unbind r
          when ((length vs1, length vs2) /= (length is1, length is2)) $ 
              typeError $ "Wrong index arity for counter " ++ show p0
          let l' = substs (zip is1 vs1) $ substs (zip is2 vs2) $ l
          tc <- view tcScope
          case tc of
            TcGhost -> typeError $ "Must be in a def for the counter"
            TcDef l2 -> do
                l1' <- normLocality l'
                l2' <- normLocality l2
                assert ("Wrong locality for counter") $ l1' `aeq` l2'
      Nothing -> typeError $ "Unknown counter: " ++ show p0

getROStrictness :: NameExp -> Check ROStrictness 
getROStrictness ne = 
    case ne^.val of
      NameConst _ pth@(PRes (PDot p n)) _ -> do
          md <- openModule p
          case lookup n (md^.nameDefs) of
            Nothing -> typeError $ "Unknown name: " ++ show (owlpretty pth)
            Just b_nd -> do
                ((is, ps), nd) <- unbind b_nd
                case nd of
                  RODef strictness _ -> return strictness
                  _ -> typeError $ "Not an RO name: " ++ show (owlpretty ne)
      _ -> typeError $ "Not an RO name: " ++ show (owlpretty ne)


getROPreimage :: Path -> ([Idx], [Idx]) -> [AExpr] -> Check AExpr
getROPreimage pth@(PRes (PDot p n)) (is, ps) as = do
    md <- openModule p
    case lookup n (md^.nameDefs) of
      Nothing -> typeError $ "Unknown name: " ++ n
      Just b_nd -> do
          ((ixs, pxs), nd') <- unbind b_nd
          assert ("Wrong index arity for name: " ++ n) $ (length ixs, length pxs) == (length is, length ps)
          let nd = substs (zip ixs is) $ substs (zip pxs ps) nd' 
          case nd of
            RODef _ b -> do
                (xs, (a, _, _)) <- unbind b
                assert ("Wrong variable arity for name: " ++ n ++ ", got " ++ show (length as) ++ " but expected " ++ show (length xs)) $ length xs == length as
                return $ substs (zip xs as) a
            _ -> typeError $ "Not an RO name: " ++ n

getROPrereq :: Path -> ([Idx], [Idx]) -> [AExpr] -> Check Prop
getROPrereq pth@(PRes (PDot p n)) (is, ps) as = do
    md <- openModule p
    case lookup n (md^.nameDefs) of
      Nothing -> typeError $ "Unknown name: " ++ n
      Just b_nd -> do
          ((ixs, pxs), nd') <- unbind b_nd
          assert ("Wrong index arity for name: " ++ n) $ (length ixs, length pxs) == (length is, length ps)
          let nd = substs (zip ixs is) $ substs (zip pxs ps) nd' 
          case nd of
            RODef _ b -> do
                (xs, (_, p, _)) <- unbind b
                assert ("Wrong variable arity for name: " ++ n ++ ", got " ++ show (length as) ++ " but expected " ++ show (length xs)) $ length xs == length as
                return $ substs (zip xs as) p
            _ -> typeError $ "Not an RO name: " ++ n


    

getNameInfo :: NameExp -> Check (Maybe (NameType, Maybe [Locality]))
getNameInfo ne = withSpan (ne^.spanOf) $ do
    case ne^.val of 
     NameConst (vs1, vs2) pth@(PRes (PDot p n)) oi -> do
         md <- openModule p
         tc <- view tcScope
         forM_ vs1 checkIdxSession
         forM_ vs2 checkIdxPId
         case lookup n (md^.nameDefs)  of
           Nothing -> typeError $ show $ ErrUnknownName pth
           Just b_nd -> do
               ((is, ps), nd') <- unbind b_nd
               assert ("Wrong index arity for name " ++ show n) $ (length vs1, length vs2) == (length is, length ps)
               let nd = substs (zip is vs1) $ substs (zip ps vs2) nd' 
               case nd of
                 AbstractName -> do
                     assert ("Cannot use hash select on abstract name") $ oi `aeq` Nothing 
                     return Nothing
                 BaseDef (nt, lcls) -> do
                     assert ("Cannot use hash select on base name") $ oi `aeq` Nothing 
                     return $ Just (nt, Just lcls) 
                 RODef _ b -> do
                     (xs, (_, _, nts)) <- unbind b
                     case oi of
                       Nothing -> do
                           assert ("Missing hash select parameter for RO name") $ length nts == 1
                           assert ("Missing variable arguments for RO name") $ length xs == 0
                           return $ Just (nts !! 0, Nothing)
                       Just (as, i) -> do
                           _ <- mapM inferAExpr as
                           assert ("Hash select parameter for RO name out of bounds") $ i < length nts
                           assert ("Variable arguments for RO name incorrect") $ length as == length xs
                           return $ Just (substs (zip xs as) $ nts !! i, Nothing)
     PRFName n s -> do
         ntLclsOpt <- getNameInfo n
         case ntLclsOpt of
           Nothing -> typeError $ show $ ErrNameStillAbstract $ show $ owlpretty n
           Just (nt, _) -> 
            case nt^.val of
            NT_PRF xs -> 
                case L.find (\p -> fst p == s) xs of
                    Just (_, (_, nt')) -> return $ Just (nt, Nothing)
                    Nothing -> typeError $ show $ ErrUnknownPRF n s
            _ -> typeError $ show $ ErrWrongNameType n "prf" nt
     _ -> error $ "Unknown: " ++ show (owlpretty ne)

getRO :: Path -> Check (Bind ([IdxVar], [IdxVar]) (Bind [DataVar] (AExpr, Prop, [NameType])))
getRO p0@(PRes (PDot p s)) = do
        md <- openModule p 
        case lookup s (md^.nameDefs) of 
          Just ind -> do
              (ps, nd) <- unbind ind
              case nd of
                RODef _ res -> return $ bind ps res
                _ -> typeError $ "Not an RO name: " ++ show (owlpretty p0)
          Nothing -> typeError $ show $ ErrUnknownRO p
getRO pth = typeError $ "Unknown path: " ++ show pth

data NameKind = NK_DH | NK_Enc | NK_PKE | NK_Sig | NK_PRF | NK_MAC | NK_Nonce
    deriving Eq

getNameKind :: NameType -> NameKind
getNameKind nt = 
    case nt^.val of
      NT_DH -> NK_DH
      NT_Sig _ -> NK_Sig
      NT_Nonce -> NK_Nonce
      NT_Enc _ -> NK_Enc
      NT_StAEAD _ _ _ _ -> NK_Enc
      NT_PKE _ -> NK_PKE
      NT_MAC _ -> NK_MAC
      NT_PRF _ -> NK_PRF


getNameTypeOpt :: NameExp -> Check (Maybe NameType)
getNameTypeOpt ne = do
    ntLclsOpt <- getNameInfo ne
    case ntLclsOpt of
        Nothing -> return Nothing
        Just (nt, _) -> return $ Just nt

getNameType :: NameExp -> Check NameType
getNameType ne = do
    ntOpt <- getNameTypeOpt ne
    case ntOpt of
        Nothing -> typeError $ show $ ErrNameStillAbstract $ show $ owlpretty ne
        Just nt -> return nt




pushLogTypecheckScope :: Check ()
pushLogTypecheckScope = do
    r <- view $ typeCheckLogDepth
    n <- liftIO $ readIORef r
    liftIO $ writeIORef r (n+1)

popLogTypecheckScope :: Check ()
popLogTypecheckScope = do
    r <- view $ typeCheckLogDepth
    n <- liftIO $ readIORef r
    liftIO $ writeIORef r (n-1)

logTypecheck :: String -> Check ()
logTypecheck s = do
    b <- view $ envFlags . fLogTypecheck
    when b $ do
        r <- view $ typeCheckLogDepth
        n <- liftIO $ readIORef r
        liftIO $ putStrLn $ replicate (n*2) ' ' ++ s
    bd <- view $ envFlags . fDebug
    case bd of
      Just fname -> do 
          r <- view $ debugLogDepth
          n <- liftIO $ readIORef r
          liftIO $ appendFile fname $ replicate (n) ' ' ++ s ++ "\n"
      Nothing -> return ()

getTyDef :: Path -> Check TyDef
getTyDef (PRes (PDot p s)) = do
    md <- openModule p
    case lookup s (md ^. tyDefs) of
      Just td -> return td
      Nothing -> typeError $ "Unknown type variable: " ++ show s 

-- AExpr's have unambiguous types, so can be inferred.

getDefSpec :: Path -> Check (Bind ([IdxVar], [IdxVar]) DefSpec)
getDefSpec (PRes (PDot p s)) = do
    md <- openModule p
    case lookup s (md^.defs) of
      Nothing -> typeError $ "Unknown def: " ++ s
      Just (DefHeader _) -> typeError $ "Def is unspecified: " ++ s
      Just (Def r) -> return r

getUserFunc :: Path -> Check (Maybe UserFunc)
getUserFunc f@(PRes (PDot p s)) = do
    fs <- view detFuncs
    case (p, lookup s fs) of
      (PTop, Just _) -> return Nothing
      (_, Nothing) -> do
          md <- openModule p
          return $ lookup s (md ^. userFuncs) 

getFuncInfo :: Path -> Check (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX)
getFuncInfo f@(PRes (PDot p s)) = do
    fs <- view detFuncs
    case (p, lookup s fs) of
      (PTop, Just r) -> return r
      (_, Nothing) -> do 
          md <- openModule p
          case lookup s (md ^. userFuncs) of 
            Just uf -> do 
                uf_interp <- view interpUserFuncs
                uf_interp p md uf
            Nothing -> typeError  (show $ ErrUnknownFunc f)
      _ -> typeError $ "Unknown function: " ++ show f

mkConcats :: [AExpr] -> AExpr
mkConcats [] = aeApp (topLevelPath "unit") [] []
mkConcats (x:xs) = 
    let go x y = aeApp (topLevelPath "concat") [] [x, y] in
    foldl go x xs

-- Find the corresponding len const associated to a name expression's name type
lenConstOfROName :: NameExp -> Check AExpr 
lenConstOfROName ne = do
    ntLclsOpt <- getNameInfo ne
    case ntLclsOpt of
      Nothing -> typeError $ "Name shouldn't be abstract: " ++ show (owlpretty ne)
      Just (nt, _) -> 
          case nt^.val of
            NT_Nonce -> return $ mkSpanned $ AELenConst "nonce"
            NT_Enc _ -> return $ mkSpanned $ AELenConst "enckey"
            NT_StAEAD _ _ _ _ -> return $ mkSpanned $ AELenConst "enckey"
            NT_MAC _ -> return $ mkSpanned $ AELenConst "mackey"
            _ -> typeError $ "Name not an RO name: " ++ show (owlpretty ne)

normalizeAExpr :: AExpr -> Check AExpr
normalizeAExpr ae = withSpan (ae^.spanOf) $ 
    case ae^.val of
      AEVar _ _ -> return ae
      AEHex _ -> return ae
      AEInt _ -> return ae
      AELenConst _ -> return ae
      AEPackIdx i a -> do
          a' <- normalizeAExpr a
          return $ Spanned (ae^.spanOf) $ AEPackIdx i a'
      AEGetVK ne -> do
          ne' <- normalizeNameExp ne
          return $ Spanned (ae^.spanOf) $ AEGetVK ne'
      AEGetEncPK ne -> do
          ne' <- normalizeNameExp ne
          return $ Spanned (ae^.spanOf) $ AEGetEncPK ne'
      AEGet ne -> do
          ne' <- normalizeNameExp ne
          return $ Spanned (ae^.spanOf) $ AEGet ne'
      AEPreimage p ps@(p1, p2) args -> do  
          ts <- view tcScope
          forM_ p1 checkIdxSession
          forM_ p2 checkIdxPId
          getROPreimage p ps args 
      AEApp f fs aes -> do
          aes' <- mapM normalizeAExpr aes
          fs' <- forM fs $ \f ->
              case f of
                ParamAExpr a -> ParamAExpr <$> normalizeAExpr a
                _ -> return f
          pth <- normalizePath f
          ouf <- getUserFunc pth
          case ouf of
            Just (FunDef b) -> normalizeAExpr =<< extractFunDef b fs' aes'
            _ -> return $ Spanned (ae^.spanOf) $ AEApp pth fs' aes'

simplifyProp :: Prop -> Check Prop
simplifyProp p = do
    p' <- go p
    if p `aeq` p' then return p' else simplifyProp p'
        where 
            go p = case p^.val of
                     PTrue -> return p
                     PFalse -> return p
                     PAnd (Spanned _ PTrue) p -> simplifyProp p
                     PAnd p (Spanned _ PTrue) -> simplifyProp p
                     PAnd (Spanned _ PFalse) p -> return pFalse
                     PAnd p (Spanned _ PFalse) -> return pFalse
                     PAnd p1 p2 -> do
                         p1' <- simplifyProp p1
                         p2' <- simplifyProp p2
                         if p1' `aeq` p2' then return p1' else
                             return $ mkSpanned $ PAnd p1' p2'
                     POr (Spanned _ PTrue) p -> return pTrue
                     POr p (Spanned _ PTrue) -> return pTrue
                     POr (Spanned _ PFalse) p -> simplifyProp p
                     POr p (Spanned _ PFalse) -> simplifyProp p
                     POr p1 p2 -> do
                         p1' <- simplifyProp p1
                         p2' <- simplifyProp p2
                         if p1' `aeq` p2' then return p1' else
                             return $ mkSpanned $ POr p1' p2'
                     PImpl (Spanned _ PTrue) p -> simplifyProp p
                     PImpl _ (Spanned _ PTrue) -> return pTrue  
                     PImpl (Spanned _ PFalse) p -> return pTrue
                     PImpl p (Spanned _ PFalse) -> pNot <$> simplifyProp p
                     PImpl p1 p2 -> do 
                         p1' <- simplifyProp p1
                         p2' <- simplifyProp p2
                         return $ mkSpanned $ PImpl p1' p2'
                     PEq a1 a2 -> do
                         a1' <- normalizeAExpr a1
                         a2' <- normalizeAExpr a2
                         return $ mkSpanned $ PEq a1' a2'
                     PLetIn a xp -> do
                         (x, p) <- unbind xp
                         simplifyProp $ subst x a p
                     PNot (Spanned _ PTrue) -> return pFalse
                     PNot (Spanned _ PFalse) -> return pTrue
                     PNot p -> do
                         p' <- simplifyProp p
                         return $ mkSpanned $ PNot p'
                     _ -> return p

      




inferAExpr :: AExpr -> Check Ty
inferAExpr ae = withSpan (ae^.spanOf) $ do
    case ae^.val of
      AEVar _ x -> do 
        tC <- view tyContext
        case lookup x tC of 
          Just (_, _, t) -> return t
          Nothing -> typeError $ show $ ErrUnknownVar x
      (AEApp f params args) -> do
        ts <- mapM inferAExpr args
        (ar, k) <- getFuncInfo f
        assert (show $ owlpretty "Wrong arity for " <> owlpretty f) $ length ts == ar
        mkSpanned <$> k params (zip args ts)
      (AEHex s) -> return $ tData zeroLbl zeroLbl
      (AEInt i) -> return $ tData zeroLbl zeroLbl
      (AELenConst s) -> do
          assert ("Unknown length constant: " ++ s) $ s `elem` ["nonce", "DH", "enckey", "pkekey", "sigkey", "prfkey", "mackey", "signature", "vk", "maclen", "tag", "counter", "crh", "group"]
          return $ tData zeroLbl zeroLbl
      (AEPackIdx idx@(IVar _ i) a) -> do
            _ <- local (set tcScope TcGhost) $ inferIdx idx
            t <- inferAExpr a
            return $ mkSpanned $ TExistsIdx $ bind i t 
      AEPreimage p ps@(p1, p2) args -> do
          ts <- view tcScope
          assert (show $ owlpretty "Preimage in non-ghost context") $ ts `aeq` TcGhost
          forM_ p1 checkIdxSession
          forM_ p2 checkIdxPId
          _ <- mapM inferAExpr args
          aes <- getROPreimage p ps args 
          inferAExpr aes
      (AEGet ne_) -> do
          ne <- normalizeNameExp ne_
          ts <- view tcScope
          ntLclsOpt <- getNameInfo ne
          case ntLclsOpt of
            Nothing -> typeError $ show $ ErrNameStillAbstract $ show $ owlpretty ne
            Just (_, ls) -> do
                ls' <- case ls of
                        Just xs -> mapM normLocality xs
                        Nothing -> do
                            case ts of
                              TcGhost -> return []
                              TcDef _ -> typeError $ show $ owlpretty "Calling get on name " <> owlpretty ne <> owlpretty " in non-ghost context"
                ot <- case ts of
                    TcDef curr_locality -> do
                        curr_locality' <- normLocality curr_locality
                        assert (show $ owlpretty "Wrong locality for " <> owlpretty ne <> owlpretty ": Got " <> owlpretty curr_locality' <> owlpretty " but expected any of " <> owlpretty ls') $
                            any (aeq curr_locality') ls'
                        return $ tName ne
                    _ -> return $ tName ne
                case ne^.val of
                  NameConst ips pth (Just (args, i)) -> do
                      aes <- getROPreimage pth ips args
                      lenConst <- local (set tcScope TcGhost) $ lenConstOfROName $ ne
                      solvability <- solvabilityAxioms aes ne 
                      return $ mkSpanned $ TRefined (tName ne) ".res" $ bind (s2n ".res") $ 
                          pAnd (mkSpanned $ PRO aes (aeVar ".res") i)
                            (pAnd solvability $ pEq (aeLength (aeVar ".res")) lenConst)
                  _ -> return ot
      (AEGetEncPK ne) -> do
          case ne^.val of
            NameConst ([], []) _ _ -> return ()
            NameConst _ _ _ -> typeError $ "Cannot call get_encpk on indexed name"
            _ -> typeError $ "Cannot call get_encpk on random oracle or PRF name"
          ntLclsOpt <- getNameInfo ne
          case ntLclsOpt of
            Nothing -> typeError $ show $ ErrNameStillAbstract$ show $ owlpretty ne
            Just (nt, _) ->           
                case nt^.val of
                    NT_PKE _ -> return $ mkSpanned $ TEnc_PK ne
                    _ -> typeError $ show $ owlpretty "Expected encryption sk: " <> owlpretty ne
      (AEGetVK ne) -> do
          case ne^.val of
            NameConst ([], []) _ _ -> return ()
            NameConst _ _ _ -> typeError $ "Cannot call get_vk on indexed name"
            _ -> typeError $ "Cannot call get_vk on random oracle or PRF name"
          ntLclsOpt <- getNameInfo ne
          case ntLclsOpt of
            Nothing -> typeError $ show $ ErrNameStillAbstract $ show $ owlpretty ne
            Just (nt, _) ->          
                case nt^.val of
                    NT_Sig _ -> return $ mkSpanned $ TVK ne
                    _ -> typeError $ show $ owlpretty "Expected signature sk: " <> owlpretty ne

splitConcats :: AExpr -> [AExpr]
splitConcats a = 
    case a^.val of
      AEApp f _ xs | f `aeq` topLevelPath "concat" -> concatMap splitConcats xs
      _ -> [a]

-- If the random oracle preimage is corrupt, then the RO is as well.
-- N.B.: this list does _not_ have to be exhaustive. It is only used to
-- prune impossible paths. We still need to case on the RO label
solvabilityAxioms :: AExpr -> NameExp -> Check Prop
solvabilityAxioms ae roName = local (set tcScope TcGhost) $ do
    ae' <- resolveANF ae
    let args = splitConcats ae'
    arg_t <- mapM inferAExpr args
    -- If all labels are corrupt, the RO is corrupt
    p <- derivabilitySufficient (zip args arg_t)
    let ax1 = pImpl p (pFlow (nameLbl roName) advLbl)
    strictness <- getROStrictness roName
    let doStrictness = case (strictness, roName^.val) of
                         (ROStrict (Just is), NameConst _ _ (Just (_, i))) -> i `elem` is
                         (ROStrict Nothing, _) -> True
                         _ -> False
    ax2 <- case doStrictness of
             True -> do 
                p' <- derivabilityNecessary (zip args arg_t)
                return $ pImpl (pFlow (nameLbl roName) advLbl) p'
             _ -> return $ pTrue
    return $ pAnd ax1 ax2

resolveANF :: AExpr -> Check AExpr
resolveANF a = do
    case a^.val of
      AEVar s x -> do 
          tC <- view tyContext 
          case lookup x tC of
            Nothing -> error $ "Unknown var during ANF: " ++ show x ++ ", " ++ show s 
            Just (_, ianf, _) -> 
                case ianf of 
                  Nothing -> return a
                  Just a' -> resolveANF a'
      AEApp f ps args -> do
          args' <- mapM resolveANF args
          return $ mkSpanned $ AEApp f ps args'
      AEHex _ -> return a
      AEPreimage f ps args -> do
          args' <- mapM resolveANF args
          return $ mkSpanned $ AEPreimage f ps args'
      AEGet _ -> return a
      AEGetEncPK _ -> return a
      AEGetVK _ -> return a
      AEPackIdx i a2 -> do
          a2' <- resolveANF a2
          return $ mkSpanned $ AEPackIdx i a2'
      AELenConst _ -> return a
      AEInt _ -> return a

-- derivabilitySufficient produces an overapproximation of when the arguments can be
-- derived, in the sense that derivabilitySufficient ==> arguments must be
-- derivable.
-- We currently approximate it since we do not precisely track weak secrecy.

data DerivabilityApproximation = DSufficient | DNecessary
    deriving Eq

derivabilitySufficient :: [(AExpr, Ty)] -> Check Prop
derivabilitySufficient args = derivability DSufficient args
--
-- derivabilityNecessary produces an overapproximationg of when the arguments can be
-- derived, in the sense that "arguments are derivable" ==> derivabilitySufficient.
-- We only use this one for strict RO names, where the name is only corrupt when
-- the preimage is derivable.

derivabilityNecessary :: [(AExpr, Ty)] -> Check Prop
derivabilityNecessary args = derivability DNecessary args

derivability :: DerivabilityApproximation -> [(AExpr, Ty)] -> Check Prop
derivability da args = do
    ps <- forM args $ \(a, t) -> do
        a' <- resolveANF a
        if isConstant a' then return pTrue else
            case (stripRefinements t)^.val of
              TName n -> return $ pFlow (nameLbl n) advLbl
              TSS n m -> return $ pOr (pFlow (nameLbl n) advLbl) (pFlow (nameLbl m) advLbl)
              TDH_PK _ -> return $ pTrue -- DH public keys always derivable
              _ -> return $ if da == DSufficient then pFalse else pTrue
    return $ foldr pAnd pTrue ps

isConstant :: AExpr -> Bool
isConstant a = 
    case a^.val of
      AEApp _ _ xs -> and $ map isConstant xs
      AEHex _ -> True
      AEInt _ -> True
      AELenConst _ -> True
      AEPackIdx _ a -> isConstant a
      _ -> False


getEnumParams :: [FuncParam] -> Check ([Idx])
getEnumParams ps = forM ps $ \p -> 
     case p of
       ParamIdx i _ -> return i
       _ -> typeError $ "Wrong param on enum: " ++ show p

getStructParams :: [FuncParam] -> Check [Idx]
getStructParams ps =
    forM ps $ \p -> do
        case p of
            ParamIdx i _ -> return i
            _ -> typeError $ "Wrong param on struct: " ++ show p

getFunDefParams :: [FuncParam] -> Check ([Idx], [Idx])
getFunDefParams [] = return ([], [])
getFunDefParams (p:ps) =
    case p of
      ParamIdx i oann -> do
          t <- inferIdx i
          (xs, ys) <- getFunDefParams ps
          case oann of
            Nothing -> 
              case t of
                IdxSession -> return (i:xs, ys)
                IdxPId -> return (xs, i:ys)
                _ -> typeError $ "Unknown index type for function param"
            Just IdxSession -> do
                checkIdxSession i
                return (i:xs, ys)
            Just IdxPId -> do
                checkIdxPId i
                return (xs, i:ys)
            Just IdxGhost -> typeError $ "Index should be annotated with session or pid here"
      _ -> typeError $ "Function parameter must be an index"

extractFunDef :: Bind (([IdxVar], [IdxVar]), [DataVar]) AExpr -> [FuncParam] -> [AExpr] -> Check AExpr 
extractFunDef b ps as = do
    (is, ps) <- getFunDefParams ps
    (((ixs, pxs), xs), a) <- unbind b
    assert ("Wrong index arity for fun def") $ (length ixs, length pxs) == (length is, length ps)
    assert ("Wrong arity for fun def") $ length xs == length as
    return $ substs (zip ixs is) $ substs (zip pxs ps) $ substs (zip xs as) a

extractAAD :: NameExp -> AExpr -> Check Prop
extractAAD ne a = do
    ni <- getNameInfo ne
    case ni of
      Nothing -> typeError $ "Unknown name type: " ++ show ne
      Just (nt, _) -> 
          case nt^.val of
            NT_StAEAD _ yp _ _ -> do
                (y, p) <- unbind yp
                return $ subst y a p
            _ -> typeError $ "Wrong name type for extractAAD: " ++ show ne

extractPredicate :: Path -> [Idx] -> [AExpr] -> Check Prop
extractPredicate pth@(PRes (PDot p s)) is as = do  
    md <- openModule p
    case lookup s (md^.predicates) of
      Nothing -> typeError $ "Unknown predicate: " ++ (show $ owlpretty pth)
      Just b -> do
          ((ixs, xs), p) <- unbind b
          assert ("Wrong index arity for predicate " ++ show (owlpretty pth)) $ length ixs == length is
          assert ("Wrong arity for predicate " ++ show (owlpretty pth)) $ length xs == length as
          return $ substs (zip ixs is) $ substs (zip xs as) p

extractEnum :: [FuncParam] -> String -> (Bind [IdxVar] [(String, Maybe Ty)]) -> Check ([(String, Maybe Ty)])
extractEnum ps s b = do
    idxs <- getEnumParams ps
    (is, bdy') <- unbind b
    assert (show $ owlpretty "Wrong index arity for enum " <> owlpretty s) $ length idxs == length is  
    let bdy = substs (zip is idxs) bdy'
    return bdy

extractStruct :: [FuncParam] -> String -> (Bind [IdxVar] [(String, Ty)]) -> Check [(String, Ty)]
extractStruct ps s b = do
    idxs <- getStructParams ps
    (is, xs') <- unbind b
    assert (show $ owlpretty "Wrong index arity for struct " <> owlpretty s <> owlpretty ": got " <> owlpretty idxs <> owlpretty " expected " <> owlpretty (length is)) $ length idxs == length is 
    return $ substs (zip is idxs) xs'



coveringLabel' :: Ty -> Check Label
coveringLabel' t = 
    case t^.val of
      (TData l _ _) -> return l
      (TDataWithLength l a) -> do
          t <- inferAExpr a
          l' <- coveringLabel' t
          return $ joinLbl l l'
      TBool l -> return l
      TUnit -> return $ zeroLbl
      (TRefined t1 _ _) -> coveringLabel' t1
      (TOption t) -> coveringLabel' t  
      (TName n) -> return $ nameLbl n
      (TVK n) -> return $ advLbl
      (TDH_PK n) -> return $ advLbl
      (TEnc_PK n) -> return $ advLbl
      (TSS n m) -> return $ joinLbl (nameLbl n) (nameLbl m) -- TODO: is this right? Definitely sound
      (TUnion t1 t2) -> do
          l1 <- coveringLabel' t1
          l2 <- coveringLabel' t2
          return $ joinLbl l1 l2
      (TConst s ps) -> do
          td <- getTyDef  s
          case td of
            EnumDef b -> do
                bdy <- extractEnum ps (show s) b
                ls <- mapM coveringLabel' $ catMaybes $ map snd bdy
                let l2 = foldr joinLbl zeroLbl ls
                return $ l2
            TyAbstract -> return $ joinLbl (lblConst $ TyLabelVar s) advLbl
            TyAbbrev t -> coveringLabel' t
            StructDef ixs -> do
                xs <- extractStruct ps (show s) ixs
                ls <- forM xs $ \(_, t) -> coveringLabel' t
                return $ foldr joinLbl zeroLbl ls
      TAdmit -> return $ zeroLbl -- mostly a placeholder
      TCase _ t1 t2 -> do -- If the covering label is the same, then we just return it. Otherwise we fail
          l1 <- coveringLabel' t1
          l2 <- coveringLabel' t2
          if (l1 `aeq` l2) then return l1 else 
              typeError $ show $ owlpretty "Difficult case for coveringLabel': TCase" <+> owlpretty l1 <+> owlpretty l2
      TExistsIdx xt -> do
          (x, t) <- unbind xt
          l <- local (over (inScopeIndices) $ insert x IdxGhost) $ coveringLabel' t
          let l1 = mkSpanned $ LRangeIdx $ bind x l
          return $ joinLbl advLbl l1

tyInfo :: Ty -> OwlDoc
tyInfo t = 
    case (stripRefinements t)^.val of
      TData _ _ os -> case unignore os of
                        Just s -> annotate (color corrColor) $ (pretty " ") <> (parens $ owlpretty s)
                        _ -> mempty
      _ -> mempty

owlprettyTyContext :: Map DataVar (Ignore String, (Maybe AExpr), Ty) -> OwlDoc
owlprettyTyContext e = vsep $ map (\(x, (s, oanf, t)) -> 
    owlpretty (unignore s) <> tyInfo t <> owlpretty ":" <+> owlpretty t) e

owlprettyIndices :: Map IdxVar IdxType -> OwlDoc
owlprettyIndices m = vsep $ map (\(i, it) -> owlpretty "index" <+> owlpretty i <> owlpretty ":" <+> owlpretty it) m

owlprettyContext :: Env -> OwlDoc
owlprettyContext e =
    vsep [owlprettyIndices (e^.inScopeIndices), owlprettyTyContext (e^.tyContext)]

isNameDefRO :: Path -> Check Bool
isNameDefRO (PRes (PDot p n)) = do 
    md <- openModule p
    case lookup n (md^.nameDefs) of
        Nothing -> typeError  $ "SMT error"
        Just b_nd -> do 
            case snd (unsafeUnbind b_nd) of
              RODef _ _ -> return True
              _ -> return False

normalizeNameExp :: NameExp -> Check NameExp
normalizeNameExp ne = 
    case ne^.val of
      NameConst ips p oi -> do
          case oi of
            Just _ -> return ne
            Nothing -> do
              isRO <- isNameDefRO p
              if isRO then return (Spanned (ne^.spanOf) $ NameConst ips p (Just ([], 0)))
                      else return ne
      PRFName ne1 s -> do
          ne' <- normalizeNameExp ne1
          return $ Spanned (ne^.spanOf) $ PRFName ne' s

-- Traversing modules to collect global info

collectEnvInfo :: (ModBody -> Map String a) -> Check (Map ResolvedPath a)
collectEnvInfo f = do
    cms <- view openModules
    res <- forM cms $ \(op, mb) -> do
        let p = case op of
                  Nothing -> PTop
                  Just n -> PPathVar OpenPathVar n
        go f p mb 
    mc <- view modContext
    res' <- forM mc $ \(x, md) -> do
        case md of
          MFun _ _ _ -> return []
          MAlias _ -> return []
          MBody xmb -> do
              let p = PPathVar (ClosedPathVar (ignore $ show x)) x
              (y, mb) <- unbind xmb
              go f (PPathVar (ClosedPathVar $ ignore $ show x) x) (subst y p mb)
    return $ concat $ res ++ res'
        where
            go :: (ModBody -> Map String a) -> ResolvedPath -> ModBody -> Check (Map ResolvedPath a)
            go f p mb = do 
                let fs = map (\(s, f) -> (PDot p s, f)) (f mb)
                fs' <- forM (mb^.modules) $ \(s, md) -> do
                    case md of
                      MFun _ _ _ -> return []
                      MAlias _ -> return []
                      MBody xmb -> do
                        (x, mb) <- unbind xmb
                        go f (PDot p s) (subst x (PDot p s) mb)
                return $ fs ++ concat fs'

-- Just concat the stuff together
collectEnvAxioms :: (ModBody -> [a]) -> Check [a]
collectEnvAxioms f = do
    cms <- view openModules
    res <- forM cms $ \(op, md) -> do
        let p = case op of
                  Nothing -> PTop
                  Just n -> PPathVar OpenPathVar n
        go f p md 
    mc <- view modContext
    res' <- forM mc $ \(x, md) -> do
        case md of
          MFun _ _ _ -> return []
          MAlias _ -> return []
          MBody xmb -> do
              let p = PPathVar (ClosedPathVar $ ignore $ show x) x
              (y, mb) <- unbind xmb
              go f (PPathVar (ClosedPathVar $ ignore $ show x) x) (subst y p mb)
    return $ concat $ res ++ res' 
        where
            go f p md = do
                let xs = f md
                ys <- forM (md^.modules) $ \(s, md) -> do
                    case md of
                      MFun _ _ _ -> return []
                      MAlias _ -> return []
                      MBody xmb -> do
                        (x, mb) <- unbind xmb
                        go f (PDot p s) (subst x (PDot p s) mb)
                return $ xs ++ concat ys


collectNameDefs :: Check (Map ResolvedPath (Bind ([IdxVar], [IdxVar]) NameDef))
collectNameDefs = collectEnvInfo (_nameDefs)

collectFlowAxioms :: Check ([(Label, Label)])
collectFlowAxioms = collectEnvAxioms (_flowAxioms)

collectAdvCorrConstraints :: Check ([Bind ([IdxVar], [DataVar]) (Label, Label)])
collectAdvCorrConstraints = collectEnvAxioms (_advCorrConstraints)

collectUserFuncs :: Check (Map ResolvedPath UserFunc)
collectUserFuncs = collectEnvInfo (_userFuncs)

collectTyDefs :: Check (Map ResolvedPath TyDef)
collectTyDefs = collectEnvInfo _tyDefs


collectROPreimages :: Check [(ResolvedPath, Bind (([IdxVar], [IdxVar]), [DataVar]) (AExpr, Prop))]
collectROPreimages = do
    xs <- collectNameDefs
    ps <- mapM go xs
    return $ concat ps
        where
            go (p, b) = do
                (is, nd) <- unbind b
                case nd of
                  RODef _ b -> do
                      (xs, (a, b, _)) <- unbind b
                      return [(p, bind (is, xs) (a, b))]
                  _ -> return []


collectLocalROPreimages :: Check [(String, Bind (([IdxVar], [IdxVar]), [DataVar]) (AExpr, Prop))]
collectLocalROPreimages =  do
    xs <- view $ curMod . nameDefs
    ps <- mapM go xs
    return $ concat ps
        where
            go (n, b) = do
                (is, nd) <- unbind b
                case nd of
                  RODef _ b -> do
                      (xs, (a, b, _)) <- unbind b
                      return [(n, bind (is, xs) (a, b))]
                  _ -> return []


pathPrefix :: ResolvedPath -> ResolvedPath
pathPrefix (PDot p _) = p
pathPrefix _ = error "pathPrefix error" 

-- Normalize and check locality
normLocality :: Locality -> Check Locality
normLocality loc@(Locality (PRes (PDot p s)) xs) = do
    md <- openModule p
    case lookup s (md^.localities) of 
      Nothing -> typeError $ "Unknown locality: " ++ show (owlpretty  loc)
      Just (Right p') -> normLocality $ Locality (PRes p') xs
      Just (Left ar) -> do
              assert (show $ owlpretty "Wrong arity for locality " <> owlpretty loc) $ ar == length xs
              forM_ xs $ \i -> do
                  it <- inferIdx i
                  assert (show $ owlpretty "Index should be ghost or party ID: " <> owlpretty i) $ (it == IdxGhost) || (it == IdxPId)
              return $ Locality (PRes (PDot p s)) xs 
normLocality loc = typeError $ "bad case: " ++ show loc

-- Normalize locality path, get arity
normLocalityPath :: Path -> Check Int
normLocalityPath (PRes loc@(PDot p s)) = do
    md <- openModule p
    case lookup s (md^.localities) of 
      Nothing -> typeError $ "Unknown locality: " ++ show loc
      Just (Left ar) -> return ar
      Just (Right p) -> normLocalityPath (PRes p)

normModulePath :: ResolvedPath -> Check ResolvedPath
normModulePath PTop = return PTop
normModulePath p@(PPathVar OpenPathVar _) = return p
normModulePath p = do
    md <- getModDef  p
    case md of
      MAlias p' -> normModulePath p'
      _ -> return p

normResolvedPath :: ResolvedPath -> Check ResolvedPath
normResolvedPath (PDot p' s) = do
    p'' <- normModulePath p'
    return $ PDot p'' s
normResolvedPath p = normModulePath p

normalizePath :: Path -> Check Path
normalizePath (PRes p) = PRes <$> normResolvedPath p
normalizePath _ = error "normalizePath: unresolved path"

getModDefFVs :: ModDef -> [Name ResolvedPath]
getModDefFVs = toListOf fv

getModBodyFVs :: ModBody -> [Name ResolvedPath]
getModBodyFVs = toListOf fv

-- Unfolds macros

owlprettyMap :: OwlPretty a => String -> Map String a -> OwlDoc
owlprettyMap s m = 
    owlpretty s <> owlpretty ":::" <+> lbracket <> line <>
    foldr (\(k, a) acc -> 
        acc <> 
        owlpretty k <> owlpretty "::" <> line <> 
        owlpretty "   " <> owlpretty a <+> comma <> line) (owlpretty "") m
    <> line <> rbracket <> line

instance OwlPretty Def where
    owlpretty (DefHeader x) = 
        let (ivars, loc) = owlprettyBind x in
        owlpretty "DefHeader:" <+> angles ivars <> owlpretty "@" <> loc
    owlpretty (Def x) =
        let (ivars, defspec) = owlprettyBind x in
        owlpretty "Def:" <+> angles ivars <> defspec

instance OwlPretty UserFunc where
    owlpretty u = owlpretty $ show u

-- debug hack
instance OwlPretty (Bind ([IdxVar], [IdxVar]) (Maybe (NameType, [Locality]))) where
    owlpretty b =
        let (ivars, opt) = owlprettyBind b in
        angles ivars <> owlpretty ":" <> opt

instance OwlPretty (Either Int ResolvedPath) where
    owlpretty (Left i) = owlpretty "Left" <+> owlpretty i
    owlpretty (Right rp) = owlpretty "Right" <+> owlpretty rp

instance OwlPretty (Embed Ty) where
    owlpretty t = owlpretty (unembed t)

instance OwlPretty DefSpec where
    owlpretty ds = 
        let abs = if unignore $ ds ^. isAbstract then owlpretty "abstract" else owlpretty "" in
        let loc = owlpretty (ds ^. defLocality) in
        let (args, (req, retTy, body)) = unsafeUnbind (ds ^. preReq_retTy_body) in
        let body' = case body of
                Nothing -> owlpretty ""
                Just e  -> owlpretty e
        in
        abs <> owlpretty "@" <> loc <> owlpretty ":" <+> owlpretty args <> owlpretty "->" <> owlpretty retTy <+> owlpretty "=" <> line <> body'




