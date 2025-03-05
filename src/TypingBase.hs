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
import Data.Time.Clock
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
      TcGhost Bool -- Bool is if crypto lemmas are allowed
      | TcDef Locality
      deriving (Show, Generic, Typeable)

instance Alpha TcScope

instance OwlPretty TcScope where
    owlpretty (TcGhost b)  = owlpretty "ghost"
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
    _preReq_retTy_body :: DepBind (Prop, Ty, Maybe Expr)
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
      | AbbrevNameDef (Bind [DataVar] NameExp)
      deriving (Show, Generic, Typeable)

instance Alpha NameDef
instance Subst ResolvedPath NameDef
instance Subst Idx NameDef

data CorrConstraint = CorrImpl Label Label | CorrGroup [Label]
    deriving (Show, Generic, Typeable)

instance OwlPretty CorrConstraint where
    owlpretty (CorrImpl l1 l2) = owlpretty "corr" <+> owlpretty l1 <+> owlpretty "==>" <+> owlpretty l2
    owlpretty (CorrGroup ls) = owlpretty "corr_group" <+> owlpretty ls

instance Alpha CorrConstraint
instance Subst Idx CorrConstraint
instance Subst ResolvedPath CorrConstraint

data ModBody = ModBody { 
    _isModuleType :: IsModuleType,
    _localities :: Map String (Either Int ResolvedPath), -- left is arity; right is if it's a synonym
    _defs :: Map String Def, 
    _tableEnv :: Map String (Ty, Locality),
    _flowAxioms :: [(Label, Label)],
    _predicates :: Map String (Bind ([IdxVar], [DataVar]) Prop),
    _advCorrConstraints :: [Bind ([IdxVar], [DataVar]) CorrConstraint],
    _tyDefs :: Map TyVar TyDef,
    -- _odh    :: Map String (Bind ([IdxVar], [IdxVar]) (NameExp, NameExp, KDFBody)),
    _nameTypeDefs :: Map String (Bind (([IdxVar], [IdxVar]), [DataVar]) NameType),
    _userFuncs :: Map String UserFunc,
    _nameDefs :: Map String (Bind ([IdxVar], [IdxVar]) NameDef), 
    _ctrEnv :: Map String (Bind ([IdxVar], [IdxVar]) Locality),
    _modules :: Map String ModDef
}
    deriving (Show, Generic, Typeable)

instance Alpha ModBody
instance Subst ResolvedPath ModBody

data MemoEntry senv = MemoEntry { 
    _memoInferAExpr :: IORef (M.Map (AlphaOrd AExpr) Ty),
    _memoNormalizeTy :: IORef (M.Map (AlphaOrd Ty) Ty),
    _memoNormalizeProp :: IORef (M.Map (AlphaOrd Prop) Prop),
    _memoisSubtype' :: IORef (M.Map (AlphaOrd (Ty, Ty)) Bool),
    _memotryFlowsTo' :: IORef (M.Map (AlphaOrd (Label, Label)) (Maybe Bool)),
    _memoTyFlowsTo' :: IORef (M.Map (AlphaOrd (Ty, Label)) Bool),
    _memoCoveringLabel' :: IORef (M.Map (AlphaOrd Ty) Label),
    _memogetNameInfo :: IORef (M.Map (AlphaOrd NameExp) (Maybe (NameType, Maybe (ResolvedPath, [Locality])))),
    _memoSolverEnv :: IORef (Maybe senv)
}

data Env senv = Env { 
    -- These below must only be modified by the trusted functions, since memoization
    -- depends on them
    _inScopeIndices ::  Map IdxVar (Ignore String, IdxType),
    _tyContext :: Map DataVar (Ignore String, (Maybe AExpr), Ty),
    _pathCondition :: [Prop],
    _expectedTy :: Maybe Ty,
    ------
    _envFlags :: Flags,
    _detFuncs :: Map String (Int, [FuncParam] -> [(AExpr, Ty)] -> Check' senv TyX), 
    _tcScope :: TcScope,
    _endpointContext :: [EndpointVar],
    _openModules :: Map (Maybe (Name ResolvedPath)) ModBody, 
    _modContext :: Map (Name ResolvedPath) ModDef,
    _interpUserFuncs :: ResolvedPath -> ModBody -> UserFunc -> Check' senv (Int, [FuncParam] -> [(AExpr, Ty)] -> Check' senv TyX),
    -- in scope atomic localities, eg "alice", "bob"; localities :: S.Set String -- ok
    _freshCtr :: IORef Integer,
    _smtCache :: IORef (M.Map Int Bool),
    _memoStack :: [MemoEntry senv],
    _z3Options :: M.Map String String, 
    _z3Results :: IORef (Map String P.Z3Result),
    _typeCheckLogDepth :: IORef Int,
    _debugLogDepth :: IORef Int,
    _typeErrorHook :: (forall a. String -> Check' senv a),
    _checkNameTypeHook :: (NameType -> Check' senv ()),
    _normalizeTyHook :: Ty -> Check' senv Ty,
    _normalizePropHook :: Prop -> Check' senv Prop,
    _decidePropHook :: Prop -> Check' senv (Maybe Bool),
    _curDef :: Maybe String,
    _tcRoutineStack :: [String],
    _inTypeError :: Bool,
    _inSMT :: Bool,
    _curSpan :: Position
}


data TyDef = 
    EnumDef (Bind [IdxVar] [(String, Maybe Ty)])
      | StructDef (Bind [IdxVar] (DepBind ()))
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

newtype Check' senv a = Check { unCheck :: ReaderT (Env senv) (ExceptT (Env senv) IO) a }
    deriving (Functor, Applicative, Monad, MonadReader (Env senv), MonadIO)


makeLenses ''DefSpec

makeLenses ''MemoEntry

makeLenses ''Env

makeLenses ''ModBody

modDefKind :: ModDef -> Check' senv IsModuleType
modDefKind (MBody xd) =
    let (_, d) = unsafeUnbind xd in return $ _isModuleType d
modDefKind (MFun _ _ xd) = 
    let (_, d) = unsafeUnbind xd in modDefKind d
modDefKind (MAlias p) = do
    md <- getModDef p
    modDefKind md




makeModDefConcrete :: ModDef -> Check' senv ModDef
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

instance Fresh (Check' senv) where
    fresh (Fn s _) = do
        r <- view freshCtr
        n <- liftIO $ readIORef r
        liftIO $ writeIORef r (n + 1)
        return $ (Fn s n)
    fresh nm@(Bn {}) = return nm

instance MonadFail (Check' senv) where
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

writeSMTCache :: Check' senv ()
writeSMTCache = do
    cacheref <- view smtCache
    cache <- liftIO $ readIORef cacheref
    filepath <- view $ envFlags . fFilePath
    let hintsFile = filepath ++ ".smtcache"
    liftIO $ BS.writeFile hintsFile $ encode cache

loadSMTCache :: Check' senv ()
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

timeCheck :: Float -> String -> Check' senv a -> Check' senv a
timeCheck threshold s k = do
    t <- liftIO $ getCurrentTime
    res <- k
    t' <- liftIO $ getCurrentTime
    let dt = diffUTCTime t' t
    when (dt > realToFrac threshold) $ liftIO $ putStrLn $ "Time for " ++ s ++ ": " ++ show dt
    return res



warn :: String -> Check' senv ()
warn msg = liftIO $ putStrLn $ "Warning: " ++ msg

--instance (Monad m, MonadIO m, MonadReader (Env senv) m) => Fresh m where

freshVar :: Check' senv String
freshVar = do
    r <- view freshCtr
    i <- liftIO $ readIORef r
    liftIO $ writeIORef r (i + 1)
    return $ ".x" ++ show i

freshIdx :: Check' senv String
freshIdx = do
    r <- view freshCtr
    i <- liftIO $ readIORef r
    liftIO $ writeIORef r (i + 1)
    return $ ".i" ++ show i

freshLbl :: Check' senv String
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
    
assert :: String -> Bool -> Check' senv ()
assert m b = do
    if b then return () else typeError m 

laxAssertion :: Check' senv () -> Check' senv ()
laxAssertion k = do
    b1 <- view $ envFlags . fLax
    onlyCheck <- view $ envFlags . fOnlyCheck
    cd <- view curDef
    let b2 = case onlyCheck of
               Just s -> (cd /= Just s) -- Only lax if onlyCheck' senv is Just s, and we are not in method s
               Nothing -> False
    if b1 || b2 then return () else k

-- withVars xs k = add xs to the typing environment, continue as k with extended
-- envrionment

withVars :: (MonadIO m, MonadReader (Env senv) m) => [(DataVar, (Ignore String, (Maybe AExpr), Ty))] -> m a -> m a
withVars assocs k = do
    local (over tyContext $ addVars assocs) $ withNewMemo $ k

pushPathCondition :: Prop -> Check' senv a -> Check' senv a
pushPathCondition p k =
    local (over pathCondition $ (p:)) $ withNewMemo $ k

withIndices :: (MonadIO m, MonadReader (Env senv) m) => [(IdxVar, (Ignore String, IdxType))] -> m a -> m a
withIndices assocs k = do
    local (over inScopeIndices $ \a -> assocs ++ a) $ withNewMemo $ k

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

curMod :: Lens' (Env senv) ModBody
curMod = openModules . unsafeHead . _2

curMemo :: Lens' (Env senv) (MemoEntry senv)
curMemo = memoStack . unsafeHead

mkMemoEntry :: IO (MemoEntry senv)
mkMemoEntry = do 
    r <- newIORef M.empty
    r2 <- newIORef M.empty
    r3 <- newIORef M.empty
    r4 <- newIORef M.empty
    r5 <- newIORef M.empty
    r6 <- newIORef M.empty
    r7 <- newIORef M.empty
    r8 <- newIORef M.empty
    r9 <- newIORef Nothing
    return $ MemoEntry r r2 r3 r4 r5 r6 r7 r8 r9

withNewMemo :: (MonadIO m, MonadReader (Env senv) m) => m a -> m a
withNewMemo k = do
    memos <- view memoStack
    memo' <- liftIO $ mkMemoEntry 
    local (over memoStack (memo':)) k

curModName :: Check' senv ResolvedPath
curModName = do
    (k, _) <- head <$> view openModules
    case k of
      Nothing -> return PTop
      Just pv -> return $ PPathVar OpenPathVar pv

withSpan :: (Ignore Position) -> Check' senv a -> Check' senv a
withSpan x k = do
        res <- local (set curSpan (unignore x)) k
        return res


inferIdx :: Idx -> Check' senv IdxType
inferIdx (IVar pos iname i) = do
    let go k = 
            if unignore pos == def then k else withSpan pos k
    go $ do
        m <- view $ inScopeIndices
        tc <- view tcScope
        case lookup i m of
          Just (_, t) -> 
              case (tc, t) of
                (TcDef _, IdxGhost) ->  
                    typeError $ "Index should be nonghost: " ++ show (owlpretty iname) 
                _ -> return t
          Nothing -> typeError $ "Unknown index: " ++ show (owlpretty iname) 

checkIdx :: Idx -> Check' senv ()
checkIdx i = do
    _ <- inferIdx i
    return ()

checkIdxSession :: Idx -> Check' senv ()
checkIdxSession i@(IVar pos _ _) = do
    it <- inferIdx i
    tc <- view tcScope
    case tc of
       TcGhost _ -> assert (show $ owlpretty "Wrong index type: " <> owlpretty i <> owlpretty ", got " <> owlpretty it <+> owlpretty " expected Ghost or Session ID") $ it /= IdxPId
       TcDef _ ->  assert (show $ owlpretty "Wrong index type: " <> owlpretty i <> owlpretty ", got " <> owlpretty it <+> owlpretty " expected Session ID") $ it == IdxSession

checkIdxPId :: Idx -> Check' senv ()
checkIdxPId i@(IVar pos _ _) = do
    it <- inferIdx i
    tc <- view tcScope
    case tc of
       TcGhost _ -> assert (show $ owlpretty "Wrong index type: " <> owlpretty i <> owlpretty ", got " <> owlpretty it <+> owlpretty " expected Ghost or PId") $ it /= IdxSession
       TcDef _ -> assert (show $ owlpretty "Wrong index type: " <> owlpretty i <> owlpretty ", got " <> owlpretty it <+> owlpretty "expected PId") $ it == IdxPId

openModule :: ResolvedPath -> Check' senv ModBody
openModule rp = do
    mb <- go rp
    tc <- view tcScope
    case tc of
      TcDef _ -> assert ("Module must be concrete: " ++ show rp) $ (mb^.isModuleType) == ModConcrete 
      _ -> return ()
    return mb
    where
        go :: ResolvedPath -> Check' senv ModBody
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

getModDef :: ResolvedPath -> Check' senv ModDef
getModDef rp = do
    go rp
    where
        go :: ResolvedPath -> Check' senv ModDef
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

checkCounterIsLocal :: Path -> ([Idx], [Idx]) -> Check' senv ()
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
            TcGhost _ -> typeError $ "Must be in a def for the counter"
            TcDef l2 -> do
                l1' <- normLocality l'
                l2' <- normLocality l2
                assert ("Wrong locality for counter") $ l1' `aeq` l2'
      Nothing -> typeError $ "Unknown counter: " ++ show p0

-- inKDFBody :: KDFBody -> AExpr -> AExpr -> AExpr -> Check' senv Prop
-- inKDFBody kdfBody salt info self = do
--     (((sx, x), (sy, y), (sz, z)), cases') <- unbind kdfBody
--     let cases = subst x salt $ subst y info $ subst z self $ cases'
--     bs <- forM cases $ \bcase -> do
--         (xs, (p, _)) <- unbind bcase
--         return $ mkExistsIdx xs p
--     return $ foldr pOr pFalse bs
-- 
-- inODHProp :: AExpr -> AExpr -> AExpr -> Check' senv Prop
-- inODHProp salt ikm info = do
--     let dhCombine x y = mkSpanned $ AEApp (topLevelPath "dh_combine") [] [x, y]
--     let dhpk x = mkSpanned $ AEApp (topLevelPath "dhpk") [] [x]
--     cur_odh <- view $ curMod . odh
--     ps <- forM cur_odh $ \(_, bnd2) -> do
--         ((is, ps), (ne1, ne2, kdfBody)) <- unbind bnd2
--         let pd1 = pEq ikm (dhCombine (dhpk $ mkSpanned $ AEGet ne1)
--                                                           (mkSpanned $ AEGet ne2)
--                                                )
--         pd2 <- inKDFBody kdfBody salt info ikm
--         return $ mkExistsIdx (is ++ ps) $ pd1 `pAnd` pd2
--     return $ foldr pOr pFalse ps

--getROStrictness :: NameExp -> Check' senv ROStrictness 
--getROStrictness ne = 
--    case ne^.val of
--      NameConst _ pth@(PRes (PDot p n)) _ -> do
--          md <- openModule p
--          case lookup n (md^.nameDefs) of
--            Nothing -> typeError $ "Unknown name: " ++ show (owlpretty pth)
--            Just b_nd -> do
--                ((is, ps), nd) <- unbind b_nd
--                case nd of
--                  RODef strictness _ -> return strictness
--                  _ -> typeError $ "Not an RO name: " ++ show (owlpretty ne)
--      _ -> typeError $ "Not an RO name: " ++ show (owlpretty ne)


--getROPreimage :: Path -> ([Idx], [Idx]) -> [AExpr] -> Check' senv AExpr
--getROPreimage pth@(PRes (PDot p n)) (is, ps) as = do
--    md <- openModule p
--    case lookup n (md^.nameDefs) of
--      Nothing -> typeError $ "Unknown name: " ++ n
--      Just b_nd -> do
--          ((ixs, pxs), nd') <- unbind b_nd
--          assert ("Wrong index arity for name: " ++ n) $ (length ixs, length pxs) == (length is, length ps)
--          let nd = substs (zip ixs is) $ substs (zip pxs ps) nd' 
--          case nd of
--            RODef _ b -> do
--                (xs, (a, _, _)) <- unbind b
--                assert ("Wrong variable arity for name: " ++ n ++ ", got " ++ show (length as) ++ " but expected " ++ show (length xs)) $ length xs == length as
--                return $ substs (zip xs as) a
--            _ -> typeError $ "Not an RO name: " ++ n
--
--getROPrereq :: Path -> ([Idx], [Idx]) -> [AExpr] -> Check' senv Prop
--getROPrereq pth@(PRes (PDot p n)) (is, ps) as = do
--    md <- openModule p
--    case lookup n (md^.nameDefs) of
--      Nothing -> typeError $ "Unknown name: " ++ n
--      Just b_nd -> do
--          ((ixs, pxs), nd') <- unbind b_nd
--          assert ("Wrong index arity for name: " ++ n) $ (length ixs, length pxs) == (length is, length ps)
--          let nd = substs (zip ixs is) $ substs (zip pxs ps) nd' 
--          case nd of
--            RODef _ b -> do
--                (xs, (_, p, _)) <- unbind b
--                assert ("Wrong variable arity for name: " ++ n ++ ", got " ++ show (length as) ++ " but expected " ++ show (length xs)) $ length xs == length as
--                return $ substs (zip xs as) p
--            _ -> typeError $ "Not an RO name: " ++ n

-- Resolves all App nodes
normalizeNameType :: NameType -> Check' senv NameType
normalizeNameType nt = pushRoutine "normalizeNameType" $  
    case nt^.val of
      NT_App p is as -> resolveNameTypeApp p is as >>= normalizeNameType
      -- NT_KDF pos bcases -> do
      --     (((sx, x), (sy, y), (sz, z)), cases) <- unbind bcases
      --     cases' <- withVars 
      --       [(x, (ignore sx, Nothing, tGhost)), 
      --        (y, (ignore sy, Nothing, tGhost)), 
      --        (z, (ignore sz, Nothing, tGhost))] $ forM cases $ \bcase -> do 
      --           (is, (p, nts)) <- unbind bcase
      --           withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) is) $ do
      --               nts' <- forM nts $ \(str, nt) -> do
      --                   nt' <- normalizeNameType nt
      --                   return (str, nt')
      --               return $ bind is (p, nts')
      --     return $ Spanned (nt^.spanOf) $ NT_KDF pos (bind ((sx, x), (sy, y), (sz, z)) cases')
      _ -> return nt

pushRoutine :: MonadReader (Env senv) m => String -> m a -> m a
pushRoutine s k = do
    b <- view $ envFlags . fLogTypecheck
    if b then 
        local (over tcRoutineStack $ (s:)) k
    else k

getNameInfo :: NameExp -> Check' senv (Maybe (NameType, Maybe (ResolvedPath, [Locality])))
getNameInfo = withMemoize (memogetNameInfo) $ \ne -> pushRoutine "getNameInfo" $ withSpan (ne^.spanOf) $ do
    res <- case ne^.val of 
             NameConst (vs1, vs2) pth@(PRes (PDot p n)) as -> do
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
                         AbbrevNameDef bne2 -> do
                             (xs, ne2) <- unbind bne2
                             assert ("Wrong arity for name abbreviation") $ length as == length xs
                             _ <- mapM inferAExpr as
                             getNameInfo $ substs (zip xs as) ne2
                         AbstractName -> do
                             assert ("Value parameters not allowed for abstract names") $ length as == 0
                             return Nothing
                         BaseDef (nt, lcls) -> do
                             assert ("Value parameters not allowed for base names") $ length as == 0
                             return $ Just (nt, Just (PDot p n, lcls)) 
             -- KDFName a b c nks j nt ib -> do
             --     _ <- local (set tcScope $ TcGhost False) $ mapM inferAExpr [a, b, c]
             --     when (not $ unignore ib) $ do
             --         nth <- view checkNameTypeHook
             --         nth nt
             --     assert ("Name kind row index out of scope") $ j < length nks
             --     return $ Just (nt, Nothing)
    case res of
      Nothing -> return Nothing
      Just (nt, lcls) -> do
          nt' <- normalizeNameType nt
          return $ Just (nt', lcls)

-- getODHNameInfo :: Path -> ([Idx], [Idx]) -> AExpr -> AExpr -> KDFSelector -> Int -> Check' senv (NameExp, NameExp, Prop, [(KDFStrictness, NameType)])
-- getODHNameInfo (PRes (PDot p s)) (is, ps) a c (i, is_case) j = do
--     let dhCombine x y = mkSpanned $ AEApp (topLevelPath "dh_combine") [] [x, y]
--     let dhpk x = mkSpanned $ AEApp (topLevelPath "dhpk") [] [x]
--     mapM_ checkIdxSession is
--     mapM_ checkIdxPId ps
--     mapM_ inferIdx is_case
--     md <- openModule p
--     case lookup s (md^.odh) of
--       Nothing -> typeError $ "Unknown ODH handle: " ++ show s
--       Just bd -> do
--           ((ixs, pxs), bdy) <- unbind bd
--           assert ("KDF index arity mismatch") $ (length ixs, length pxs) == (length is, length ps)
--           let (ne1, ne2, kdfBody) = substs (zip ixs is) $ substs (zip pxs ps) $ bdy
--           let b = dhCombine (dhpk (aeGet ne1)) (aeGet ne2)
--           (((sx, x), (sy, y), (sz, z)), cases) <- unbind kdfBody
--           assert ("Number of KDF case mismatch") $ i < length cases
--           let bpcases  = subst x a $ subst y c $ subst z b $ cases !! i
--           (xs_case, pcases')  <- unbind bpcases
--           assert ("KDF case index arity mismatch") $ length xs_case == length is_case
--           let (p, cases') = substs (zip xs_case is_case) pcases'
--           assert ("KDF name row mismatch") $ j < length cases'
--           return (ne1, ne2, p, cases')


getNameKind :: NameType -> Check' senv NameKind
getNameKind nt = 
    case nt^.val of
      NT_DH ->    return $ NK_DH
      NT_Sig _ -> return $ NK_Sig
      NT_Nonce l -> return $ NK_Nonce l
      NT_Enc _ -> return $ NK_Enc
      NT_StAEAD _ _ _ _ -> return $ NK_Enc
      NT_PKE _ -> return $ NK_PKE
      NT_MAC _ -> return $ NK_MAC
      NT_App p ps as -> resolveNameTypeApp p ps as >>= getNameKind
      -- NT_KDF _ _ -> return $ NK_KDF
    
resolveNameTypeApp :: Path -> ([Idx], [Idx]) -> [AExpr] -> Check' senv NameType
resolveNameTypeApp pth@(PRes (PDot p s)) (is, ps) as = do
    forM_ is checkIdxSession
    forM_ ps checkIdxPId
    forM_ as inferAExpr
    md <- openModule p
    case lookup s (md ^. nameTypeDefs) of 
      Nothing -> typeError $ "Unknown name type: " ++ show (owlpretty pth)
      Just bnd -> do
          (((xs, ys), args), nt) <- unbind bnd
          assert ("Wrong index arity on name type: " ++ show (owlpretty pth)) $ (length is, length ps) == (length xs, length ys)
          assert ("Wrong var arity on name type") $ length args == length as
          return $ substs (zip xs is) $ substs (zip ys ps) $ substs (zip args as) $ nt
resolveNameTypeApp pth _ _ = typeError $ "Uhoh: " ++ show (owlpretty pth)


getNameTypeOpt :: NameExp -> Check' senv (Maybe NameType)
getNameTypeOpt ne = do
    ntLclsOpt <- getNameInfo ne
    case ntLclsOpt of
        Nothing -> return Nothing
        Just (nt, _) -> return $ Just nt

getNameType :: NameExp -> Check' senv NameType
getNameType ne = do
    ntOpt <- getNameTypeOpt ne
    case ntOpt of
        Nothing -> typeError $ show $ ErrNameStillAbstract $ show $ owlpretty ne
        Just nt -> return nt

pushLogTypecheckScope :: Check' senv ()
pushLogTypecheckScope = do
    r <- view $ typeCheckLogDepth
    n <- liftIO $ readIORef r
    liftIO $ writeIORef r (n+1)

popLogTypecheckScope :: Check' senv ()
popLogTypecheckScope = do
    r <- view $ typeCheckLogDepth
    n <- liftIO $ readIORef r
    liftIO $ writeIORef r (n-1)

withPushLog :: Check' senv a -> Check' senv a
withPushLog k = do
    pushLogTypecheckScope
    r <- k
    popLogTypecheckScope
    return r

logTypecheck :: OwlDoc -> Check' senv ()
logTypecheck s = do
    b <- view $ envFlags . fLogTypecheck
    when b $ do
        r <- view $ typeCheckLogDepth
        n <- liftIO $ readIORef r
        liftIO $ putDoc $ owlpretty (replicate (n*2) ' ') <> align s <> line
    bd <- view $ envFlags . fDebug
    case bd of
      Just fname -> do 
          r <- view $ debugLogDepth
          n <- liftIO $ readIORef r
          liftIO $ appendFile fname $ replicate (n) ' ' ++ show s ++ "\n"
      Nothing -> return ()

getTyDef :: Path -> Check' senv TyDef
getTyDef (PRes (PDot p s)) = do
    md <- openModule p
    case lookup s (md ^. tyDefs) of
      Just td -> return td
      Nothing -> typeError $ "Unknown type variable: " ++ show s 

-- AExpr's have unambiguous types, so can be inferred.

getDefSpec :: Path -> Check' senv (Bind ([IdxVar], [IdxVar]) DefSpec)
getDefSpec (PRes (PDot p s)) = do
    md <- openModule p
    case lookup s (md^.defs) of
      Nothing -> typeError $ "Unknown def: " ++ s
      Just (DefHeader _) -> typeError $ "Def is unspecified: " ++ s
      Just (Def r) -> return r

getUserFunc :: Path -> Check' senv (Maybe UserFunc)
getUserFunc f@(PRes (PDot p s)) = do
    fs <- view detFuncs
    case (p, lookup s fs) of
      (PTop, Just _) -> return Nothing
      (_, Nothing) -> do
          md <- openModule p
          return $ lookup s (md ^. userFuncs) 

getFuncInfo :: Path -> Check' senv (Int, [FuncParam] -> [(AExpr, Ty)] -> Check' senv TyX)
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
lenConstOfUniformName :: NameExp -> Check' senv AExpr 
lenConstOfUniformName ne = do
    ntLclsOpt <- getNameInfo ne
    case ntLclsOpt of
      Nothing -> typeError $ "Name shouldn't be abstract: " ++ show (owlpretty ne)
      Just (nt, _) -> go nt
    where
        go nt = case nt^.val of
                    NT_Nonce l -> return $ mkSpanned $ AELenConst l
                    NT_Enc _ -> return $ mkSpanned $ AELenConst "enckey"
                    NT_StAEAD _ _ _ _ -> return $ mkSpanned $ AELenConst "enckey"
                    NT_MAC _ -> return $ mkSpanned $ AELenConst "mackey"
                    -- NT_KDF _ _ -> return $ mkSpanned $ AELenConst "kdfkey"
                    NT_App p ps as -> resolveNameTypeApp p ps as >>= go
                    _ -> typeError $ "Name not uniform: " ++ show (owlpretty ne)

normalizeAExpr :: AExpr -> Check' senv AExpr
normalizeAExpr ae = pushRoutine "normalizeAExpr" $ withSpan (ae^.spanOf) $ 
    case ae^.val of
      AEVar _ _ -> return ae
      AEHex _ -> return ae
      AEInt _ -> return ae
      -- AEKDF a b c nks j -> do
      --     a' <- normalizeAExpr a
      --     b' <- normalizeAExpr b
      --     c' <- normalizeAExpr c
      --     return $ Spanned (ae^.spanOf) $ AEKDF a' b' c' nks j
      AELenConst _ -> return ae
      AEGetVK ne -> do
          ne' <- normalizeNameExp ne
          return $ Spanned (ae^.spanOf) $ AEGetVK ne'
      AEGetEncPK ne -> do
          ne' <- normalizeNameExp ne
          return $ Spanned (ae^.spanOf) $ AEGetEncPK ne'
      AEGet ne -> do
          ne' <- normalizeNameExp ne
          return $ Spanned (ae^.spanOf) $ AEGet ne'
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

withMemoize :: (Alpha a, OwlPretty a, OwlPretty b) => (Lens' (MemoEntry senv) (IORef (M.Map (AlphaOrd a) b))) -> (a -> Check' senv b) -> a -> Check' senv b
withMemoize lns k x = do
    memo <- view $ curMemo . lns
    mp <- liftIO $ readIORef memo
    case M.lookup (AlphaOrd x) mp of
      Just v -> return v
      Nothing -> do
          v <- k x
          liftIO $ modifyIORef memo $ M.insert (AlphaOrd x) v
          return v

lengthConstants :: [String]
lengthConstants = ["nonce", "DH", "enckey", "pke_sk", "sigkey", "kdfkey", "mackey", "signature", "pke_pk", "vk", "maclen", "tag", "counter", "crh", "group"]

inferAExpr :: AExpr -> Check' senv Ty
inferAExpr = withMemoize memoInferAExpr $ \ae -> withSpan (ae^.spanOf) $ pushRoutine ("inferAExpr " ++ (show $ owlpretty ae)) $ do
    case ae^.val of
      AEVar _ x -> do 
        tC <- view tyContext
        case lookup x tC of 
          Just (_, _, t) -> return t
          Nothing -> do
              local (set inTypeError True) $ typeError $ show $ ErrUnknownVar x
      (AEApp f params args) -> do
        ts <- local (set expectedTy Nothing) $ mapM inferAExpr args
        (ar, k) <- getFuncInfo f
        assert (show $ owlpretty "Wrong arity for " <> owlpretty f) $ length ts == ar
        insmt <- view inSMT
        if insmt then mkSpanned <$> k params (zip args ts)
                else
                    openArgs (zip args ts) $ \args' -> 
                        mkSpanned <$> k params args'
      (AEHex s) -> do
          assert ("HexConst must have even length") $ length s `mod` 2 == 0
          return $ tData zeroLbl zeroLbl
      (AEInt i) -> return $ tData zeroLbl zeroLbl
      -- (AEKDF a b c nks j) -> do
      --     _ <- local (set expectedTy Nothing) $ mapM inferAExpr [a, b, c]
      --     assert ("name kind index out of bounds") $ j < length nks
      --     return $ tGhost
      (AELenConst s) -> do
          assert ("Unknown length constant: " ++ s) $ s `elem` lengthConstants 
          return $ tData zeroLbl zeroLbl
      (AEGet ne_) -> do
          ne <- normalizeNameExp ne_
          ts <- view tcScope
          ntLclsOpt <- getNameInfo ne
          ot <- case ntLclsOpt of
            Nothing ->
                case ts of
                  TcGhost _ -> return $ tName ne
                  _ -> typeError $ show $ ErrNameStillAbstract $ show $ owlpretty ne
            Just (_, ls) -> do
                ls' <- case ls of
                        Just (_, xs) -> mapM normLocality xs
                        Nothing -> do
                            case ts of
                              TcGhost _ -> return []
                              TcDef _ -> typeError $ show $ owlpretty "Calling get on name " <> owlpretty ne <> owlpretty " in non-ghost context"
                case ts of
                    TcDef curr_locality -> do
                        curr_locality' <- normLocality curr_locality
                        if null ls' then 
                                    typeError $ "Cannot call get on ghost name: " ++ show (owlpretty ne)
                                    else 
                                    assert (show $ owlpretty "Wrong locality for " <> owlpretty ne <> owlpretty ": Got " <> owlpretty curr_locality' <> owlpretty " but expected any of " <> owlpretty ls') $
                            any (aeq curr_locality') ls'
                        return $ tName ne
                    _ -> return $ tName ne
          return ot 
      (AEGetEncPK ne) -> do
          case ne^.val of
            NameConst ([], []) _ _ -> return ()
            NameConst _ _ _ -> typeError $ "Cannot call get_encpk on indexed name"
            _ -> typeError $ "Cannot call get_encpk on PRF name" 
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
            _ -> typeError $ "Cannot call get_vk on PRF name"
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

resolveANF :: AExpr -> Check' senv AExpr
resolveANF a = do
    case a^.val of
      AEVar s x -> do 
          tC <- view tyContext 
          case lookup x tC of
            Nothing -> do
                tC <- view tyContext
                typeError $ "Unknown var: " ++ show x ++ ", " ++ unignore s
            Just (_, ianf, _) -> 
                case ianf of 
                  Nothing -> return a
                  Just a' -> resolveANF a'
      AEApp f ps args -> do
          args' <- mapM resolveANF args
          return $ mkSpanned $ AEApp f ps args'
      AEHex _ -> return a
      --AEPreimage f ps args -> do
      --    args' <- mapM resolveANF args
      --    return $ mkSpanned $ AEPreimage f ps args'
      AEGet _ -> return a
      AEGetEncPK _ -> return a
      AEGetVK _ -> return a
      AELenConst _ -> return a
      AEInt _ -> return a
      -- AEKDF a b c nks j -> do
      --     a' <- resolveANF a
      --     b' <- resolveANF b
      --     c' <- resolveANF c
      --     return $ mkSpanned $ AEKDF a' b' c' nks j

isConstant :: AExpr -> Bool
isConstant a = 
    case a^.val of
      AEApp _ _ xs -> and $ map isConstant xs
      AEHex _ -> True
      AEInt _ -> True
      AELenConst _ -> True
      _ -> False


getEnumParams :: [FuncParam] -> Check' senv ([Idx])
getEnumParams ps = forM ps $ \p -> 
     case p of
       ParamIdx i _ -> return i
       _ -> typeError $ "Wrong param on enum: " ++ show p

getStructParams :: [FuncParam] -> Check' senv [Idx]
getStructParams ps =
    forM ps $ \p -> do
        case p of
            ParamIdx i _ -> return i
            _ -> typeError $ "Wrong param on struct: " ++ show p

getFunDefParams :: [FuncParam] -> Check' senv ([Idx], [Idx])
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
                _ -> typeError $ "nknown index type for function param"
            Just IdxSession -> do
                checkIdxSession i
                return (i:xs, ys)
            Just IdxPId -> do
                checkIdxPId i
                return (xs, i:ys)
            Just IdxGhost -> typeError $ "Index should be annotated with session or pid here"
      _ -> typeError $ "Function parameter must be an index"

extractFunDef :: Bind (([IdxVar], [IdxVar]), [DataVar]) AExpr -> [FuncParam] -> [AExpr] -> Check' senv AExpr 
extractFunDef b ps as = do
    (is, ps) <- getFunDefParams ps
    (((ixs, pxs), xs), a) <- unbind b
    assert ("Wrong index arity for fun def") $ (length ixs, length pxs) == (length is, length ps)
    assert ("Wrong arity for fun def") $ length xs == length as
    return $ substs (zip ixs is) $ substs (zip pxs ps) $ substs (zip xs as) a

extractAAD :: NameExp -> AExpr -> Check' senv Prop
extractAAD ne a = do
    ni <- getNameInfo ne
    case ni of
      Nothing -> typeError $ "Unknown name type: " ++ show ne
      Just (nt, _) -> 
          case nt^.val of
            NT_StAEAD _ ysp _ _ -> do
                ((y, slf), p) <- unbind ysp
                return $ subst y a $ subst slf (aeGet ne) $ p
            _ -> typeError $ "Wrong name type for extractAAD: " ++ show ne

extractPredicate :: Path -> [Idx] -> [AExpr] -> Check' senv Prop
extractPredicate pth@(PRes (PDot p s)) is as = do  
    md <- openModule p
    case lookup s (md^.predicates) of
      Nothing -> typeError $ "Unknown predicate: " ++ (show $ owlpretty pth)
      Just b -> do
          ((ixs, xs), p) <- unbind b
          assert ("Wrong index arity for predicate " ++ show (owlpretty pth)) $ length ixs == length is
          assert ("Wrong arity for predicate " ++ show (owlpretty pth)) $ length xs == length as
          return $ substs (zip ixs is) $ substs (zip xs as) p

tryObtainTyCases :: Ty -> Check' senv (Maybe (ResolvedPath, [(String, Maybe Ty)]))
tryObtainTyCases t = 
    case (stripRefinements t)^.val of
      TConst s@(PRes (PDot pth _)) ps -> do
          td <- getTyDef s
          case td of
            EnumDef b -> do
                vs <- extractEnum ps (show s) b
                return $ Just (pth, vs)
            _ -> return Nothing
      TOption t0 -> return $ Just (PTop, [("None", Nothing), ("Some", Just t0)])
      _ -> return Nothing

obtainTyCases :: Ty -> String -> Check' senv (ResolvedPath, [(String, Maybe Ty)])
obtainTyCases t err = do
    o <- tryObtainTyCases t
    case o of
      Just res -> return res
      Nothing -> typeError $ "Not an enum: " ++ show (owlpretty t) ++ err


extractEnum :: [FuncParam] -> String -> (Bind [IdxVar] [(String, Maybe Ty)]) -> Check' senv ([(String, Maybe Ty)])
extractEnum ps s b = do
    idxs <- getEnumParams ps
    (is, bdy') <- unbind b
    assert (show $ owlpretty "Wrong index arity for enum " <> owlpretty s) $ length idxs == length is  
    let bdy = substs (zip is idxs) bdy'
    return bdy

obtainStructInfoTopDown :: AExpr -> Ty -> Check' senv [(String, Ty)]
obtainStructInfoTopDown a t =
    case t^.val of
      TConst s@(PRes (PDot pth _)) ps -> do 
          td <- getTyDef s
          case td of
            StructDef sd -> extractStructTopDown ps s a sd
            _ -> typeError $ "Not a struct: " ++ show (owlpretty t)
      _ -> typeError $ "Not a struct: " ++ show (owlpretty t)

-- Get types of fields from struct expression 
extractStructTopDown :: [FuncParam] -> Path -> AExpr -> Bind [IdxVar] (DepBind ()) -> Check' senv [(String, Ty)]
extractStructTopDown fps spath@(PRes (PDot pth s)) struct idp = do                                       
    (is, dp) <- unbind idp
    idxs <- getStructParams fps
    assert (show $ owlpretty "Wrong index arity for struct " <> owlpretty spath <> owlpretty ": got " <> owlpretty idxs <> owlpretty " expected " <> owlpretty (length is)) $ length idxs == length is 
    go struct $ substs (zip is idxs) dp
        where
            go struct (DPDone _) = return []
            go struct (DPVar t sx xk) = do
                (x, k) <- unbind xk
                let fld = mkSpanned $ AEApp (PRes $ PDot pth sx) fps [struct]
                let t2 = tRefined t ".res" $ pEq (aeVar ".res") fld
                res <- go struct $ subst x fld k
                return $ (sx, t2) : res


coveringLabelStruct :: [FuncParam] -> Path -> Bind [IdxVar] (DepBind ()) -> Check' senv Label
coveringLabelStruct fps spath idp = do
    (is, dp) <- unbind idp
    idxs <- getStructParams fps
    assert (show $ owlpretty "Wrong index arity for struct " <> owlpretty spath <> owlpretty ": got " <> owlpretty idxs <> owlpretty " expected " <> owlpretty (length is)) $ length idxs == length is 
    go $ substs (zip is idxs) dp
        where
            go (DPDone _) = return zeroLbl
            go (DPVar t sx xk) = do
                l1 <- coveringLabel' t
                (x, k) <- unbind xk
                l2_ <- withVars [(x, (ignore sx, Nothing, t))] $ go k
                let l2 = if x `elem` toListOf fv l2_ then (mkSpanned $ LRangeVar $ bind x l2_) else l2_
                return $ joinLbl l1 l2 


coveringLabel' :: Ty -> Check' senv Label
coveringLabel' = withMemoize (memoCoveringLabel') $ \t ->  
    case t^.val of
      (TData l _ _) -> return l
      (TDataWithLength l a) -> do
          t <- inferAExpr a
          l' <- coveringLabel' t
          return $ joinLbl l l'
      TGhost -> return ghostLbl
      TBool l -> return l
      TUnit -> return $ zeroLbl
      (TRefined t1 _ _) -> coveringLabel' t1
      (TOption t) -> coveringLabel' t  
      (TName n) -> return $ nameLbl n
      (TVK n) -> return $ advLbl
      (TDH_PK n) -> return $ advLbl
      (TEnc_PK n) -> return $ advLbl
      (TSS n m) -> return $ joinLbl (nameLbl n) (nameLbl m)
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
            StructDef ixs -> coveringLabelStruct ps s ixs
      TAdmit -> return $ zeroLbl -- mostly a placeholder
      TCase _ t1 t2 -> do 
          l1 <- coveringLabel' t1
          l2 <- coveringLabel' t2
          return $ joinLbl l1 l2
      TExistsIdx s xt -> do
          (x, t) <- unbind xt
          l <- withIndices [(x, (ignore s, IdxGhost))] $ coveringLabel' t
          let l1 = mkSpanned $ LRangeIdx $ bind x l
          return $ joinLbl advLbl l1
      THexConst a -> return zeroLbl

quantFree :: Prop -> Check' senv Bool
quantFree p = 
    case p^.val of
      PQuantIdx _ _ _ -> return False
      PQuantBV _ _ _ -> return False
      PAADOf ne a -> extractAAD ne a >>= quantFree
      -- PInODH a b c -> return True -- Abstracted by a predicate in SMT
      PApp ps is xs -> return True -- Abstracted by a predicate in SMT
      PAnd p1 p2 -> liftM2 (&&) (quantFree p1) (quantFree p2)
      POr p1 p2 -> liftM2 (&&) (quantFree p1) (quantFree p2)
      PNot p1 -> quantFree p1
      PLetIn a xp -> do
          (x, p) <- unbind xp
          quantFree $ subst x a p
      _ -> return True


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

owlprettyTyContextANF :: Map DataVar (Ignore String, (Maybe AExpr), Ty) -> OwlDoc
owlprettyTyContextANF e = vsep $ map (\(x, (s, oanf, t)) -> 
    owlpretty x <> tyInfo t <> owlpretty oanf <> owlpretty ":" <+> owlpretty t) e

owlprettyIndices :: Map IdxVar (Ignore String, IdxType) -> OwlDoc
owlprettyIndices m = vsep $ map (\(i, (s, it)) -> owlpretty "index" <+> owlpretty (unignore s) <> owlpretty ":" <+> owlpretty it) m

owlprettyContext :: Env senv -> OwlDoc
owlprettyContext e =
    vsep [owlprettyIndices (e^.inScopeIndices), owlprettyTyContext (e^.tyContext)]

--isNameDefRO :: Path -> Check' senv Bool
--isNameDefRO (PRes (PDot p n)) = do 
--    md <- openModule p
--    case lookup n (md^.nameDefs) of
--        Nothing -> typeError  $ "SMT error"
--        Just b_nd -> do 
--            case snd (unsafeUnbind b_nd) of
--              RODef _ _ -> return True
--              _ -> return False

normalizeNameExp :: NameExp -> Check' senv NameExp
normalizeNameExp ne = 
    case ne^.val of
      NameConst (vs1, vs2) pth@(PRes (PDot p n)) as -> do
          md <- openModule p
          case lookup n (md^.nameDefs) of
            Nothing -> typeError $ show $ ErrUnknownName pth
            Just b_nd -> do 
                       ((is, ps), nd') <- unbind b_nd
                       let nd = substs (zip is vs1) $ substs (zip ps vs2) nd' 
                       case nd of
                         AbbrevNameDef bne2 -> do
                             (xs, ne2) <- unbind bne2
                             assert ("Wrong arity") $ length xs == length as
                             normalizeNameExp $ substs (zip xs as) ne2
                         _ -> return ne
      -- KDFName a b c nks j nt ib -> do
      --     a' <- resolveANF a >>= normalizeAExpr 
      --     b' <- resolveANF b >>= normalizeAExpr 
      --     c' <- resolveANF c >>= normalizeAExpr 
      --     nt' <- normalizeNameType nt
      --     return $ Spanned (ne^.spanOf) $ KDFName a' b' c' nks j nt' ib

-- Traversing modules to collect global info

collectEnvInfo :: (ModBody -> Map String a) -> Check' senv (Map ResolvedPath a)
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
            go :: (ModBody -> Map String a) -> ResolvedPath -> ModBody -> Check' senv (Map ResolvedPath a)
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
collectEnvAxioms :: (ModBody -> [a]) -> Check' senv [a]
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


collectNameDefs :: Check' senv (Map ResolvedPath (Bind ([IdxVar], [IdxVar]) NameDef))
collectNameDefs = collectEnvInfo (_nameDefs)

collectFlowAxioms :: Check' senv ([(Label, Label)])
collectFlowAxioms = collectEnvAxioms (_flowAxioms)

collectAdvCorrConstraints :: Check' senv ([Bind ([IdxVar], [DataVar]) CorrConstraint])
collectAdvCorrConstraints = collectEnvAxioms (_advCorrConstraints)

collectUserFuncs :: Check' senv (Map ResolvedPath UserFunc)
collectUserFuncs = collectEnvInfo (_userFuncs)

collectTyDefs :: Check' senv (Map ResolvedPath TyDef)
collectTyDefs = collectEnvInfo _tyDefs


--collectROPreimages :: Check' senv [(ResolvedPath, Bind (([IdxVar], [IdxVar]), [DataVar]) (AExpr, Prop))]
--collectROPreimages = do
--    xs <- collectNameDefs
--    ps <- mapM go xs
--    return $ concat ps
--        where
--            go (p, b) = do
--                (is, nd) <- unbind b
--                case nd of
--                  RODef _ b -> do
--                      (xs, (a, b, _)) <- unbind b
--                      return [(p, bind (is, xs) (a, b))]
--                  _ -> return []


--collectLocalROPreimages :: Check' senv [(String, Bind (([IdxVar], [IdxVar]), [DataVar]) (AExpr, Prop))]
--collectLocalROPreimages =  do
--    xs <- view $ curMod . nameDefs
--    ps <- mapM go xs
--    return $ concat ps
--        where
--            go (n, b) = do
--                (is, nd) <- unbind b
--                case nd of
--                  RODef _ b -> do
--                      (xs, (a, b, _)) <- unbind b
--                      return [(n, bind (is, xs) (a, b))]
--                  _ -> return []


pathPrefix :: ResolvedPath -> ResolvedPath
pathPrefix (PDot p _) = p
pathPrefix _ = error "pathPrefix error" 

-- Normalize and check locality
normLocality :: Locality -> Check' senv Locality
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
normLocalityPath :: Path -> Check' senv Int
normLocalityPath (PRes loc@(PDot p s)) = do
    md <- openModule p
    case lookup s (md^.localities) of 
      Nothing -> typeError $ "Unknown locality: " ++ show loc
      Just (Left ar) -> return ar
      Just (Right p) -> normLocalityPath (PRes p)

normModulePath :: ResolvedPath -> Check' senv ResolvedPath
normModulePath PTop = return PTop
normModulePath p@(PPathVar OpenPathVar _) = return p
normModulePath p = do
    md <- getModDef  p
    case md of
      MAlias p' -> normModulePath p'
      _ -> return p

normResolvedPath :: ResolvedPath -> Check' senv ResolvedPath
normResolvedPath (PDot p' s) = do
    p'' <- normModulePath p'
    return $ PDot p'' s
normResolvedPath p = normModulePath p

normalizePath :: Path -> Check' senv Path
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
        owlpretty "DefSpec"
        -- let (args, (req, retTy, body)) = unsafeUnbind (ds ^. preReq_retTy_body) in
        -- let body' = case body of
        --         Nothing -> owlpretty ""
        --         Just e  -> owlpretty e
        -- in
        -- abs <> owlpretty "@" <> loc <> owlpretty ":" <+> owlpretty args <> owlpretty "->" <> owlpretty retTy <+> owlpretty "=" <> line <> body'


caseProp :: (Prop -> a -> a -> Check' senv a) -> Prop -> (Bool -> Check' senv a) -> Check' senv a
caseProp merge p' k = do
    nph <- view normalizePropHook
    p <- nph p'
    dph <- view decidePropHook
    ob <- dph p
    case ob of
      Just True -> k True
      Just False -> k False
      Nothing -> do 
        x <- fresh $ s2n "%caseProp"
        t1 <- withPushLog $ withVars [(x, (ignore $ show x, Nothing, tLemma p))] $ pushPathCondition p $ do
            logTypecheck $ owlpretty "Case split: " <> owlpretty p
            k True
        t2 <- withPushLog $ withVars [(x, (ignore $ show x, Nothing, tLemma $ pNot p))] $ pushPathCondition (pNot p) $ do
            logTypecheck $ owlpretty "Case split: " <> owlpretty (pNot p)
            k False
        merge p t1 t2


casePropTy :: Prop -> (Bool -> Check' senv Ty) -> Check' senv Ty
casePropTy = caseProp $ \p t1 t2 -> do
    ntyHook <- view normalizeTyHook
    ntyHook $ mkSpanned $ if t1 `aeq` t2 then t1^.val else TCase p t1 t2

casePropTyList :: Prop -> (Bool -> Check' senv [Ty]) -> Check' senv [Ty]
casePropTyList = caseProp $ \p t1s t2s -> do
    assert ("casePropTyList: got unequal length lists") $ length t1s == length t2s
    ntyHook <- view normalizeTyHook
    mapM ntyHook $ if t1s `aeq` t2s then t1s else (map (\(t1, t2) -> mkSpanned $ TCase p t1 t2) (zip t1s t2s)) 

casePropTyUnspanned :: Prop -> (Bool -> Check' senv TyX) -> Check' senv TyX
casePropTyUnspanned = caseProp $ \p t1 t2 -> do
    ntyHook <- view normalizeTyHook
    t3 <- ntyHook $ mkSpanned $ if t1 `aeq` t2 then t1 else TCase p (mkSpanned t1) (mkSpanned t2)
    return $ t3^.val

stripTy :: DataVar -> Ty -> Check' senv Ty
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
      TExistsIdx s it -> do
          (i, t) <- unbind it
          t' <- stripTy x t
          return $ mkSpanned $ TExistsIdx s $ bind i t
      THexConst a -> return t


stripNameExp :: DataVar -> NameExp -> Check' senv NameExp
stripNameExp x e = 
    case e^.val of
      NameConst _ _ as -> do
          as' <- mapM resolveANF as
          if x `elem` (concat $ map getAExprDataVars as') then
            typeError $ "Cannot remove " ++ show x ++ " from the scope of " ++ show (owlpretty e)
          else
            return e 
      -- KDFName a b c nks j nt ib -> do
      --     a' <- resolveANF a
      --     b' <- resolveANF b
      --     c' <- resolveANF c
      --     if x `elem` (getAExprDataVars a' ++ getAExprDataVars b' ++ getAExprDataVars c' ++ toListOf fv nt) then 
      --        typeError $ "Cannot remove " ++ show x ++ " from the scope of " ++ show (owlpretty e)
      --     else return $ Spanned (e^.spanOf) $ KDFName a' b' c' nks j nt ib
      
stripLabel :: DataVar -> Label -> Check' senv Label
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


tyNonGhost :: Ty -> Check' senv Bool
tyNonGhost t = do
    l <- coveringLabel' t
    lblNonGhost l

lblNonGhost :: Label -> Check' senv Bool
lblNonGhost l  =
    case l^.val of
      LName _ -> return True
      LZero -> return True
      LAdv -> return True
      LTop -> return True
      LGhost -> return False
      LJoin l1 l2 -> liftM2 (&&) (lblNonGhost l1) (lblNonGhost l2)
      LConst _ -> return True
      LRangeIdx xl -> lblNonGhost $ snd $ unsafeUnbind xl
      LRangeVar xl -> lblNonGhost $ snd $ unsafeUnbind xl






-- get strongest type that doesn't mention x
-- t <= stripTy x t
-- p ==> stripProp x p 
-- l <= stripLabel x l

-- Find strongest p' such that p ==> p', and x \notin p'.
-- Always succeeds.
stripProp :: DataVar -> Prop -> Check' senv Prop
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

byCasesProp :: Prop -> (Bool -> Check' senv Bool) -> Check' senv Bool
byCasesProp = caseProp $ \_ b1 b2 -> return $ b1 && b2

openTy :: Ty -> (Ty -> Check' senv Ty) -> Check' senv Ty
openTy t k = 
    case t^.val of
      TCase p t1 t2 -> casePropTy p (\b -> openTy (if b then t1 else t2) k)
      TRefined t0 s kref -> openTy t0 $ \t0' -> k $ Spanned (t^.spanOf) $ TRefined t0' s kref
      _ -> k t

analyzeTyByCases :: Ty -> (Ty -> Check' senv ()) -> Check' senv ()
analyzeTyByCases t k = 
    case t^.val of
      TCase p t1 t2 -> caseProp (\_ _ _ -> return ()) p (\b -> analyzeTyByCases (if b then t1 else t2) k)
      TRefined t0 _ _ -> analyzeTyByCases t0 k
      _ -> k t


openArgs :: [(AExpr, Ty)] -> ([(AExpr, Ty)] -> Check' senv Ty) -> Check' senv Ty
openArgs [] k = k []
openArgs ((a, t) : args) k = 
    openTy t $ \t' -> 
        openArgs args $ \args' -> 
            k ((a, t') : args')
