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
import Error.Diagnose
import qualified Data.Set as S
import Data.Maybe
import Data.Serialize
import Data.IORef
import Control.Monad
import qualified Data.List as L
import qualified Data.Map.Strict as M
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Cont
import CmdArgs
import System.FilePath
import Prettyprinter
import Control.Lens
import Control.Lens.At
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

instance Pretty TcScope where
    pretty TcGhost = pretty "ghost"
    pretty (TcDef l) = pretty "def" <> tupled [pretty l]

data IdxType = IdxSession | IdxPId | IdxGhost
    deriving Eq

instance Pretty IdxType where
    pretty IdxSession = pretty "IdxSession"
    pretty IdxPId = pretty "IdxPId"
    pretty IdxGhost = pretty "IdxGhost"

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
    deriving (Eq, Show, Generic, Typeable)

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
      | RODef ([AExpr], [NameType])
      deriving (Show, Generic, Typeable)

instance Alpha NameDef
instance Subst ResolvedPath NameDef
instance Subst Idx NameDef

data ModBody = ModBody { 
    _isModuleType :: IsModuleType,
    _localities :: Map String (Either Int ResolvedPath), -- left is arity; right is if it's a synonym
    _defs :: Map String Def, 
    _tableEnv :: Map String (Ty, Locality),
    _flowAxioms :: [(Label, Label)],
    _advCorrConstraints :: [Bind [IdxVar] (Label, Label)],
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
    _tyContext :: Map DataVar (Ignore String, Ignore (Maybe AExpr), Ty),
    _tcScope :: TcScope,
    _endpointContext :: [EndpointVar],
    _inScopeIndices ::  Map IdxVar IdxType,
    _openModules :: Map (Maybe (Name ResolvedPath)) ModBody, 
    _modContext :: Map (Name ResolvedPath) ModDef,
    _interpUserFuncs :: Ignore Position -> ResolvedPath -> ModBody -> UserFunc -> Check (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX),
    -- in scope atomic localities, eg "alice", "bob"; localities :: S.Set String -- ok
    _freshCtr :: IORef Integer,
    _smtCache :: IORef (M.Map Int Bool),
    _z3Options :: M.Map String String, 
    _z3Results :: IORef (Map String P.Z3Result),
    _typeCheckLogDepth :: IORef Int,
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

instance Pretty (TypeError) where
    pretty (ErrWrongNameType n s nt) = 
        pretty "Wrong name type for " <> pretty n <> pretty ": expected " <> pretty s <> pretty ", got " <> pretty nt
    pretty (ErrBadArgs s ts) = 
        pretty "Bad argument types for " <> pretty s <> pretty ": got " <> pretty ts
    pretty (ErrUnknownRO s) = 
        pretty "Unknown random oracle value: " <> pretty (show s)
    pretty (ErrUnknownPRF n s) = 
        pretty "Unknown prf value for " <> pretty n <> pretty ": " <> pretty s
    pretty (ErrDuplicateVarName s) = 
        pretty "Duplicate variable name: " <> pretty s
    pretty (ErrWrongCases s a expected actual) = 
        pretty "Wrong cases for " <> pretty s <> pretty " with "  <> pretty a  <> pretty " expected " <> pretty (map fst expected) <> pretty " but got " <> pretty (map fst actual)
    pretty (ErrAssertionFailed fn p) =
        pretty "Assertion failed: " <> pretty p <> pretty " from " <> pretty fn
    pretty (ErrUnknownName s) =  
        pretty "Unknown name: " <> pretty s
    pretty (ErrUnknownFunc s) =  
        pretty "Unknown func: " <> pretty s
    pretty (ErrUnknownVar s) =  
        pretty "Unknown variable: " <> pretty s
    pretty (ErrUnknownType s) =  
        pretty "Unknown type name: " <> pretty s
    pretty (ErrFlowCheck l1 l2) =  
        pretty "Label " <> pretty l1 <> pretty " does not flow to " <> pretty l2
    pretty (ErrLenAmbiguous t) = 
        pretty "Type " <> pretty t <> pretty " has an ambiguous length"
    pretty (ErrCannotProveSubtype t1 t2) = 
        pretty "Cannot prove type " <> pretty t1 <> pretty " is a subtype of " <> pretty t2
    pretty (ErrWrongLocality n l ls) = 
        pretty "Locality of name " <> pretty n <> pretty " is not available to locality " <> pretty l
    pretty (ErrNameStillAbstract n) =
        pretty "Name" <+> pretty n <+> pretty "is abstract but needs to be concrete here"

instance Show TypeError where
    show s = show $ pretty s

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
    md <- getModDef (ignore def) p
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
    md <- getModDef (ignore def) p
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

removeAnfVars :: Map DataVar (Ignore String, Ignore (Maybe AExpr), Ty) -> Map DataVar (Ignore String, Ignore (Maybe AExpr), Ty)
removeAnfVars ctxt = L.foldl' g [] ctxt where
    g acc (v, (s, anf, t)) = case unignore anf of
        Nothing -> acc ++ [(v, (s, anf, hideAnfVarsInTy ctxt t))]
        Just _ -> acc

hideAnfVarsInTy :: Map DataVar (Ignore String, Ignore (Maybe AExpr), Ty) -> Ty -> Ty
hideAnfVarsInTy ctxt t = L.foldl' substAnfVar t ctxt where
    substAnfVar :: Ty -> (DataVar, (Ignore String, Ignore (Maybe AExpr), Ty)) -> Ty
    substAnfVar ty (v, (_, anf, _)) = do
        case unignore anf of
            Nothing -> ty
            Just anfOrig -> subst v anfOrig ty


typeError :: Ignore Position -> String -> Check a
typeError pos msg = do
    fn <- takeFileName <$> (view $ envFlags . fFilePath)
    fl <- takeDirectory <$> (view $ envFlags . fFilePath)
    f <- view $ envFlags . fFileContents
    tyc <- removeAnfVars <$> view tyContext
    let rep = Err Nothing msg [(unignore pos, This msg)] [Note $ show $ prettyTyContext tyc]
    let diag = addFile (addReport def rep) (fn) f  
    e <- ask
    printDiagnostic stdout True True 4 defaultStyle diag 
    Check $ lift $ throwError e

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


addVars :: [(DataVar, (Ignore String, Ignore (Maybe AExpr), Ty))] -> Map DataVar (Ignore String, Ignore (Maybe AExpr), Ty) -> Map DataVar (Ignore String, Ignore (Maybe AExpr), Ty)
addVars xs g = g ++ xs 
    
assert :: String -> Bool -> Check ()
assert m b = do
    if b then return () else do
        pos <- view $ curSpan
        typeError (ignore pos) m 

laxAssertion :: Check () -> Check ()
laxAssertion k = do
    l <- view $ envFlags . fLax
    if l then return () else k

-- withVars xs k = add xs to the typing environment, continue as k with extended
-- envrionment

withVars :: [(DataVar, (Ignore String, Ignore (Maybe AExpr), Ty))] -> Check a -> Check a
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

inferIdx :: Idx -> Check IdxType
inferIdx (IVar pos i) = do
    m <- view $ inScopeIndices
    tc <- view tcScope
    case lookup i m of
      Just t -> 
          case (tc, t) of
            (TcDef _, IdxGhost) ->  
                typeError pos $ "Index should be nonghost: " ++ show (pretty i) 
            _ -> return t
      Nothing -> typeError pos $ "Unknown index: " ++ show (pretty i)

checkIdx :: Idx -> Check ()
checkIdx i = do
    debug $ pretty "Checking index " <> pretty i
    _ <- inferIdx i
    return ()

checkIdxSession :: Idx -> Check ()
checkIdxSession i@(IVar pos _) = do
    it <- inferIdx i
    tc <- view tcScope
    case tc of
       TcGhost -> assert (show $ pretty "Wrong index type: " <> pretty i <> pretty ", got " <> pretty it <+> pretty " expected Ghost or Session ID") $ it /= IdxPId
       TcDef _ ->  assert (show $ pretty "Wrong index type: " <> pretty i <> pretty ", got " <> pretty it <+> pretty " expected Session ID") $ it == IdxSession

checkIdxPId :: Idx -> Check ()
checkIdxPId i@(IVar pos _) = do
    it <- inferIdx i
    tc <- view tcScope
    case tc of
       TcGhost -> assert (show $ pretty "Wrong index type: " <> pretty i <> pretty ", got " <> pretty it <+> pretty " expected Ghost or PId") $ it /= IdxSession
       TcDef _ -> assert (show $ pretty "Wrong index type: " <> pretty i <> pretty ", got " <> pretty it <+> pretty "expected PId") $ it == IdxPId

openModule :: Ignore Position -> ResolvedPath -> Check ModBody
openModule pos rp = do
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
              Just (MFun _ _ _) -> typeError pos $ show p0 ++ " is not a module"
              Nothing -> typeError pos $ "Unknown module or functor (functor argument, openModule): " ++ show p0
        go p0@(PDot p' s) = do
            md <- go p'
            case lookup s (md^.modules) of
              Just (MAlias p) -> go p
              Just (MBody xmb) -> do
                  (x, mb) <- unbind xmb
                  return $ subst x p0 mb
              Just (MFun _ _ _) -> typeError pos $ show p0 ++ " is not a module"
              Nothing -> typeError pos $ "Unknown module: " ++ show p0

stripRefinements :: Ty -> Ty
stripRefinements t =
    case t^.val of
      TRefined t _ -> stripRefinements t
      _ -> t

getModDef :: Ignore Position -> ResolvedPath -> Check ModDef
getModDef pos rp = do
    go rp
    where
        go :: ResolvedPath -> Check ModDef
        go PTop = typeError pos $ "Got top for getModDef"
        go (PPathVar OpenPathVar v) = typeError pos $ "Got opened module var for getModDef"
        go (PPathVar (ClosedPathVar _) v) = do
            mc <- view modContext
            case lookup v mc of
              Just b -> return b
              Nothing -> typeError pos $ "Unknown module or functor (functor argument, getModDef): " ++ show rp
        go p0@(PDot p' s) = do
            md <- openModule pos p'
            case lookup s (md^.modules) of
              Just b -> return b
              Nothing -> typeError pos $ "Unknown module or functor: " ++ show rp

checkCounterIsLocal :: Ignore Position -> Path -> ([Idx], [Idx]) -> Check ()
checkCounterIsLocal pos p0@(PRes (PDot p s)) (vs1, vs2) = do
    md <- openModule pos p
    case lookup s (md^.ctrEnv) of
      Just r -> do
          forM_ vs1 checkIdxSession
          forM_ vs2 checkIdxPId
          ((is1, is2), l) <- unbind r
          when ((length vs1, length vs2) /= (length is1, length is2)) $ 
              typeError pos $ "Wrong index arity for counter " ++ show p0
          let l' = substs (zip is1 vs1) $ substs (zip is2 vs2) $ l
          tc <- view tcScope
          case tc of
            TcGhost -> typeError pos $ "Must be in a def for the counter"
            TcDef l2 -> do
                l1' <- normLocality pos l'
                l2' <- normLocality pos l2
                assert ("Wrong locality for counter") $ l1' `aeq` l2'
      Nothing -> typeError pos $ "Unknown counter: " ++ show p0

getROPreimage :: Ignore Position -> Path -> ([Idx], [Idx]) -> Check [AExpr]
getROPreimage pos pth@(PRes (PDot p n)) (is, ps) = do
    md <- openModule pos p
    case lookup n (md^.nameDefs) of
      Nothing -> typeError pos $ "Unknown name: " ++ n
      Just b_nd -> do
          ((ixs, pxs), nd') <- unbind b_nd
          assert ("Wrong index arity for name: " ++ n) $ (length ixs, length pxs) == (length is, length ps)
          let nd = substs (zip ixs is) $ substs (zip pxs ps) nd' 
          case nd of
            RODef (as, _) -> return as
            _ -> typeError pos $ "Not an RO name: " ++ n



    

getNameInfo :: NameExp -> Check (Maybe (NameType, Maybe [Locality]))
getNameInfo ne = do
    debug $ pretty (unignore $ ne^.spanOf) <> pretty "Inferring name expression" <+> pretty ne 
    case ne^.val of 
     NameConst (vs1, vs2) pth@(PRes (PDot p n)) oi -> do
         md <- openModule (ne^.spanOf) p
         tc <- view tcScope
         forM_ vs1 checkIdxSession
         forM_ vs2 checkIdxPId
         case lookup n (md^.nameDefs)  of
           Nothing -> typeError (ne^.spanOf) $ show $ ErrUnknownName pth
           Just b_nd -> do
               ((is, ps), nd') <- unbind b_nd
               assert ("Wrong index arity for name " ++ show n) $ (length vs1, length vs2) == (length is, length ps)
               let nd = substs (zip is vs1) $ substs (zip ps vs2) nd' 
               case nd of
                 AbstractName -> do
                     assert ("Cannot use hash select on abstract name") $ oi == Nothing 
                     return Nothing
                 BaseDef (nt, lcls) -> do
                     assert ("Cannot use hash select on base name") $ oi == Nothing 
                     return $ Just (nt, Just lcls) 
                 RODef (as, nts) -> 
                     case oi of
                       Nothing -> do
                           assert ("Missing hash select parameter for RO name") $ length nts == 1
                           return $ Just (nts !! 0, Nothing)
                       Just i -> do
                           assert ("Hash select parameter for RO name out of bounds") $ i < length nts
                           return $ Just (nts !! i, Nothing)
     PRFName n s -> do
         ntLclsOpt <- getNameInfo n
         case ntLclsOpt of
           Nothing -> typeError (ne^.spanOf) $ show $ ErrNameStillAbstract $ show $ pretty n
           Just (nt, _) -> 
            case nt^.val of
            NT_PRF xs -> 
                case L.find (\p -> fst p == s) xs of
                    Just (_, (_, nt')) -> return $ Just (nt, Nothing)
                    Nothing -> typeError (ne^.spanOf) $ show $ ErrUnknownPRF n s
            _ -> typeError (ne^.spanOf) $ show $ ErrWrongNameType n "prf" nt
     _ -> error $ "Unknown: " ++ show (pretty ne)

getRO :: Ignore Position -> Path -> Check (Bind ([IdxVar], [IdxVar]) ([AExpr], [NameType]))
getRO pos p0@(PRes (PDot p s)) = do
        md <- openModule pos p 
        case lookup s (md^.nameDefs) of 
          Just ind -> do
              (ps, nd) <- unbind ind
              case nd of
                RODef res -> return $ bind ps res
                _ -> typeError pos $ "Not an RO name: " ++ show (pretty p0)
          Nothing -> typeError pos $ show $ ErrUnknownRO p
getRO pos pth = typeError pos $ "Unknown path: " ++ show pth


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
        Nothing -> typeError (ne^.spanOf) $ show $ ErrNameStillAbstract $ show $ pretty ne
        Just nt -> return nt


debug :: Show a => a -> Check ()
debug d = do
    b <- view $ envFlags . fDebug
    when b $ liftIO $ putStrLn $ show d

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

getTyDef :: Ignore Position -> Path -> Check TyDef
getTyDef pos (PRes (PDot p s)) = do
    md <- openModule pos p
    case lookup s (md ^. tyDefs) of
      Just td -> return td
      Nothing -> typeError pos $ "Unknown type variable: " ++ show s 

-- AExpr's have unambiguous types, so can be inferred.

getUserFunc :: Ignore Position -> Path -> Check (Maybe UserFunc)
getUserFunc pos (PRes (PDot p s)) = do
    md <- openModule pos p
    return $ lookup s (md^.userFuncs)

getDefSpec :: Ignore Position -> Path -> Check (Bind ([IdxVar], [IdxVar]) DefSpec)
getDefSpec pos (PRes (PDot p s)) = do
    md <- openModule pos p
    case lookup s (md^.defs) of
      Nothing -> typeError pos $ "Unknown def: " ++ s
      Just (DefHeader _) -> typeError pos $ "Def is unspecified: " ++ s
      Just (Def r) -> return r


getFuncInfo :: Ignore Position -> Path -> Check (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX)
getFuncInfo pos f@(PRes (PDot p s)) = do
    fs <- view detFuncs
    case (p, lookup s fs) of
      (PTop, Just r) -> return r
      (_, Nothing) -> do 
          md <- openModule pos p
          case lookup s (md ^. userFuncs) of 
            Just uf -> do 
                uf_interp <- view interpUserFuncs
                uf_interp pos p md uf
            Nothing -> typeError (pos) (show $ ErrUnknownFunc f)

mkConcats :: [AExpr] -> AExpr
mkConcats [] = aeApp (topLevelPath "UNIT") [] []
mkConcats (x:xs) = 
    let go x y = aeApp (topLevelPath "concat") [] [x, y] in
    foldl go x xs

inferAExpr :: AExpr -> Check Ty
inferAExpr ae = do
    debug $ pretty (unignore $ ae^.spanOf) <> pretty "Inferring AExp" <+> pretty ae
    case ae^.val of
      AEVar _ x -> do 
        tC <- view tyContext
        case lookup x tC of 
          Just (_, _, t) -> return t
          Nothing -> typeError (ae^.spanOf) $ show $ ErrUnknownVar x
      (AEApp f params args) -> do
        debug $ pretty "Inferring application: " <> pretty (unignore $ ae^.spanOf)
        ts <- mapM inferAExpr args
        (ar, k) <- getFuncInfo (ae^.spanOf) f
        assert (show $ pretty "Wrong arity for " <> pretty f) $ length ts == ar
        mkSpanned <$> k params (zip args ts)
      (AEString s) -> return $ tData zeroLbl zeroLbl
      (AEInt i) -> return $ tData zeroLbl zeroLbl
      (AELenConst s) -> do
          assert ("Unknown length constant: " ++ s) $ s `elem` ["nonce", "DH", "enckey", "pkekey", "sigkey", "prfkey", "mackey", "signature", "vk", "maclen", "tag"]
          return $ tData zeroLbl zeroLbl
      (AEPackIdx idx@(IVar _ i) a) -> do
            _ <- local (set tcScope TcGhost) $ inferIdx idx
            t <- inferAExpr a
            return $ mkSpanned $ TExistsIdx $ bind i t 
      AEPreimage p ps@(p1, p2) -> do
          ts <- view tcScope
          assert (show $ pretty "Preimage in non-ghost context") $ ts `aeq` TcGhost
          forM_ p1 checkIdxSession
          forM_ p2 checkIdxPId
          aes <- getROPreimage (ae^.spanOf) p ps 
          inferAExpr $ mkConcats aes
      (AEGet ne_) -> do
          ne <- normalizeNameExp ne_
          ts <- view tcScope
          ntLclsOpt <- getNameInfo ne
          case ntLclsOpt of
            Nothing -> typeError (ae^.spanOf) $ show $ ErrNameStillAbstract $ show $ pretty ne
            Just (_, ls) -> do
                ls' <- case ls of
                        Just xs -> mapM (normLocality (ae^.spanOf)) xs
                        Nothing -> do
                            case ts of
                              TcGhost -> return []
                              TcDef _ -> typeError (ae^.spanOf) $ show $ pretty "Calling get on name " <> pretty ne <> pretty " in non-ghost context"
                ot <- case ts of
                    TcDef curr_locality -> do
                        curr_locality' <- normLocality (ae^.spanOf) curr_locality
                        assert (show $ pretty "Wrong locality for " <> pretty ne <> pretty ": Got " <> pretty curr_locality' <> pretty " but expected any of " <> pretty ls') $
                            any (aeq curr_locality') ls'
                        return $ tName ne
                    _ -> return $ tName ne
                case ne^.val of
                  NameConst ips pth (Just i) -> do
                      aes <- getROPreimage (ae^.spanOf) pth ips 
                      return $ tRefined ot $ bind (s2n ".res") $ mkSpanned $ PRO (mkConcats aes) (aeVar ".res") i  
                  _ -> return ot
      (AEGetEncPK ne) -> do
          case ne^.val of
            NameConst ([], []) _ _ -> return ()
            NameConst _ _ _ -> typeError (ae^.spanOf) $ "Cannot call get_encpk on indexed name"
            _ -> typeError (ae^.spanOf) $ "Cannot call get_encpk on random oracle or PRF name"
          ntLclsOpt <- getNameInfo ne
          case ntLclsOpt of
            Nothing -> typeError (ae^.spanOf) $ show $ ErrNameStillAbstract$ show $ pretty ne
            Just (nt, _) ->           
                case nt^.val of
                    NT_PKE _ -> return $ mkSpanned $ TEnc_PK ne
                    _ -> typeError (ae^.spanOf) $ show $ pretty "Expected encryption sk: " <> pretty ne
      (AEGetVK ne) -> do
          case ne^.val of
            NameConst ([], []) _ _ -> return ()
            NameConst _ _ _ -> typeError (ae^.spanOf) $ "Cannot call get_vk on indexed name"
            _ -> typeError (ae^.spanOf) $ "Cannot call get_vk on random oracle or PRF name"
          ntLclsOpt <- getNameInfo ne
          case ntLclsOpt of
            Nothing -> typeError (ae^.spanOf) $ show $ ErrNameStillAbstract $ show $ pretty ne
            Just (nt, _) ->          
                case nt^.val of
                    NT_Sig _ -> return $ mkSpanned $ TVK ne
                    _ -> typeError (ae^.spanOf) $ show $ pretty "Expected signature sk: " <> pretty ne

getEnumParams :: Ignore Position -> [FuncParam] -> Check ([Idx])
getEnumParams pos ps = forM ps $ \p -> 
     case p of
       ParamIdx i -> return i
       _ -> typeError pos $ "Wrong param on enum: " ++ show p

getStructParams :: Ignore Position -> [FuncParam] -> Check [Idx]
getStructParams pos ps =
    forM ps $ \p -> do
        case p of
            ParamIdx i -> return i
            _ -> typeError pos $ "Wrong param on struct: " ++ show p

extractEnum :: Ignore Position -> [FuncParam] -> String -> (Bind [IdxVar] [(String, Maybe Ty)]) -> Check ([(String, Maybe Ty)])
extractEnum pos ps s b = do
    idxs <- getEnumParams pos ps
    (is, bdy') <- unbind b
    assert (show $ pretty "Wrong index arity for enum " <> pretty s) $ length idxs == length is  
    let bdy = substs (zip is idxs) bdy'
    return bdy

extractStruct :: Ignore Position -> [FuncParam] -> String -> (Bind [IdxVar] [(String, Ty)]) -> Check [(String, Ty)]
extractStruct pos ps s b = do
    idxs <- getStructParams pos ps
    (is, xs') <- unbind b
    assert (show $ pretty "Wrong index arity for struct " <> pretty s <> pretty ": got " <> pretty idxs <> pretty " expected " <> pretty (length is)) $ length idxs == length is 
    return $ substs (zip is idxs) xs'



coveringLabel' :: Ty -> Check Label
coveringLabel' t = 
    case t^.val of
      (TData l _) -> return l
      (TDataWithLength l a) -> do
          t <- inferAExpr a
          l' <- coveringLabel' t
          return $ joinLbl l l'
      TBool l -> return l
      TUnit -> return $ zeroLbl
      (TRefined t1 _) -> coveringLabel' t1
      (TOption t) -> coveringLabel' t  
      (TName n) -> return $ nameLbl n
      (TVK n) -> return $ zeroLbl
      (TDH_PK n) -> return $ zeroLbl
      (TEnc_PK n) -> return $ zeroLbl
      (TSS n m) -> return $ joinLbl (nameLbl n) (nameLbl m) -- TODO: is this right? Definitely sound
      (TUnion t1 t2) -> do
          l1 <- coveringLabel' t1
          l2 <- coveringLabel' t2
          return $ joinLbl l1 l2
      (TConst s ps) -> do
          td <- getTyDef (t^.spanOf) s
          case td of
            EnumDef b -> do
                bdy <- extractEnum (t^.spanOf) ps (show s) b
                ls <- mapM coveringLabel' $ catMaybes $ map snd bdy
                let l2 = foldr joinLbl zeroLbl ls
                return $ l2
            TyAbstract -> return $ joinLbl (lblConst $ TyLabelVar s) advLbl
            TyAbbrev t -> coveringLabel' t
            StructDef ixs -> do
                xs <- extractStruct (t^.spanOf) ps (show s) ixs
                ls <- forM xs $ \(_, t) -> coveringLabel' t
                return $ foldr joinLbl zeroLbl ls
      TAdmit -> return $ zeroLbl -- mostly a placeholder
      TCase _ t1 t2 -> do -- If the covering label is the same, then we just return it. Otherwise we fail
          l1 <- coveringLabel' t1
          l2 <- coveringLabel' t2
          if (l1 `aeq` l2) then return l1 else 
              typeError (t^.spanOf) $ show $ pretty "Difficult case for coveringLabel': TCase" <+> pretty l1 <+> pretty l2
      TExistsIdx xt -> do
          (x, t) <- unbind xt
          l <- local (over (inScopeIndices) $ insert x IdxGhost) $ coveringLabel' t
          let l1 = mkSpanned $ LRangeIdx $ bind x l
          return $ joinLbl advLbl l1

prettyTyContext :: Map DataVar (Ignore String, Ignore (Maybe AExpr), Ty) -> Doc ann
prettyTyContext e = vsep $ map (\(_, (x, _, t)) -> pretty (unignore x) <> pretty ":" <+> pretty t) e

prettyIndices :: Map IdxVar IdxType -> Doc ann
prettyIndices m = vsep $ map (\(i, it) -> pretty "index" <+> pretty i <> pretty ":" <+> pretty it) m

prettyContext :: Env -> Doc ann
prettyContext e =
    vsep [prettyIndices (e^.inScopeIndices), prettyTyContext (e^.tyContext)]

isNameDefRO :: Path -> Check Bool
isNameDefRO (PRes (PDot p n)) = do 
    md <- openModule (ignore def) p
    case lookup n (md^.nameDefs) of
        Nothing -> typeError (ignore def) $ "SMT error"
        Just b_nd -> do 
            case snd (unsafeUnbind b_nd) of
              RODef _ -> return True
              _ -> return False

normalizeNameExp :: NameExp -> Check NameExp
normalizeNameExp ne = 
    case ne^.val of
      NameConst ips p oi -> do
          case oi of
            Just _ -> return ne
            Nothing -> do
              isRO <- isNameDefRO p
              if isRO then return (Spanned (ne^.spanOf) $ NameConst ips p (Just 0))
                      else return ne
      PRFName ne1 s -> do
          ne' <- normalizeNameExp ne1
          return $ Spanned (ne^.spanOf) $ PRFName ne' s

-- Traversing modules to collect global info

instance Pretty ResolvedPath where
    pretty a = pretty $ show a

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

collectAdvCorrConstraints :: Check ([Bind [IdxVar] (Label, Label)])
collectAdvCorrConstraints = collectEnvAxioms (_advCorrConstraints)

collectUserFuncs :: Check (Map ResolvedPath UserFunc)
collectUserFuncs = collectEnvInfo (_userFuncs)

collectTyDefs :: Check (Map ResolvedPath TyDef)
collectTyDefs = collectEnvInfo _tyDefs


collectROPreimages :: Check [Bind ([IdxVar], [IdxVar]) [AExpr]]
collectROPreimages = do
    xs <- collectNameDefs
    ps <- mapM go (map snd xs)
    return $ concat ps
        where
            go b = do
                (is, nd) <- unbind b
                case nd of
                  RODef (x, _) -> return [bind is x]
                  _ -> return []


collectLocalROPreimages :: Check [Bind ([IdxVar], [IdxVar]) [AExpr]]
collectLocalROPreimages =  do
    xs <- view $ curMod . nameDefs
    ps <- mapM go (map snd xs)
    return $ concat ps
        where
            go b = do
                (is, nd) <- unbind b
                case nd of
                  RODef (x, _) -> return [bind is x]
                  _ -> return []


pathPrefix :: ResolvedPath -> ResolvedPath
pathPrefix (PDot p _) = p
pathPrefix _ = error "pathPrefix error" 

-- Normalize and check locality
normLocality :: Ignore Position -> Locality -> Check Locality
normLocality pos loc@(Locality (PRes (PDot p s)) xs) = do
    debug $ pretty "normLocality: " <> (pretty $ show loc)
    md <- openModule pos p
    case lookup s (md^.localities) of 
      Nothing -> typeError pos $ "Unknown locality: " ++ show (pretty  loc)
      Just (Right p') -> normLocality pos $ Locality (PRes p') xs
      Just (Left ar) -> do
              assert (show $ pretty "Wrong arity for locality " <> pretty loc) $ ar == length xs
              forM_ xs $ \i -> do
                  it <- inferIdx i
                  assert (show $ pretty "Index should be ghost or party ID: " <> pretty i) $ (it == IdxGhost) || (it == IdxPId)
              return $ Locality (PRes (PDot p s)) xs 
normLocality pos loc = typeError pos $ "bad case: " ++ show loc

-- Normalize locality path, get arity
normLocalityPath :: Ignore Position -> Path -> Check Int
normLocalityPath pos (PRes loc@(PDot p s)) = do
    md <- openModule pos p
    case lookup s (md^.localities) of 
      Nothing -> typeError pos $ "Unknown locality: " ++ show loc
      Just (Left ar) -> return ar
      Just (Right p) -> normLocalityPath pos (PRes p)

normModulePath :: ResolvedPath -> Check ResolvedPath
normModulePath PTop = return PTop
normModulePath p@(PPathVar OpenPathVar _) = return p
normModulePath p = do
    md <- getModDef (ignore def) p
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

prettyMap :: Pretty a => String -> Map String a -> Doc ann
prettyMap s m = 
    pretty s <> pretty ":::" <+> lbracket <> line <>
    foldr (\(k, a) acc -> 
        acc <> 
        pretty k <> pretty "::" <> line <> 
        pretty "   " <> pretty a <+> comma <> line) (pretty "") m
    <> line <> rbracket <> line


instance Pretty Def where
    pretty (DefHeader x) = 
        let (ivars, loc) = prettyBind x in
        pretty "DefHeader:" <+> angles ivars <> pretty "@" <> loc
    pretty (Def x) =
        let (ivars, defspec) = prettyBind x in
        pretty "Def:" <+> angles ivars <> defspec

instance Pretty UserFunc where
    pretty u = pretty $ show u

-- debug hack
instance Pretty (Bind ([IdxVar], [IdxVar]) (Maybe (NameType, [Locality]))) where
    pretty b =
        let (ivars, opt) = prettyBind b in
        angles ivars <> pretty ":" <> opt

instance Pretty (Either Int ResolvedPath) where
    pretty (Left i) = pretty "Left" <+> pretty i
    pretty (Right rp) = pretty "Right" <+> pretty rp

instance Pretty (Embed Ty) where
    pretty t = pretty (unembed t)

instance Pretty DefSpec where
    pretty ds = 
        let abs = if unignore $ ds ^. isAbstract then pretty "abstract" else pretty "" in
        let loc = pretty (ds ^. defLocality) in
        let (args, (req, retTy, body)) = unsafeUnbind (ds ^. preReq_retTy_body) in
        let body' = case body of
                Nothing -> pretty ""
                Just e  -> pretty e
        in
        abs <> pretty "@" <> loc <> pretty ":" <+> pretty args <> pretty "->" <> pretty retTy <+> pretty "=" <> line <> body'




