{-# LANGUAGE TemplateHaskell #-} 
{-# LANGUAGE MultiParamTypeClasses #-} 
{-# LANGUAGE GeneralizedNewtypeDeriving #-} 
{-# LANGUAGE TypeSynonymInstances #-} 
{-# LANGUAGE FlexibleInstances #-} 
{-# LANGUAGE DeriveGeneric #-}
module SMTBase where

import AST
import Data.List
import Control.Monad
import Data.Maybe
import Data.IORef
import System.Process
import System.Exit
import CmdArgs
import Data.Default (Default, def)
import System.Directory
import System.FilePath
import Control.Lens
import Control.Concurrent
import Control.Concurrent.MVar
import qualified Data.List as L
import Control.Monad.Except
import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Reader
import Data.Hashable
import qualified Data.Map.Strict as M
import qualified Data.Map.Ordered as OM
import Control.Lens
import Prettyprinter
import TypingBase
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

data SExp = 
    SAtom String
      | SApp [SExp]
      | SComment String
      | SPat SExp
      | SOption String String 

instance Show SExp where
    show (SAtom s) = s
    show (SApp xs) = " (" ++ intercalate " " (map show xs) ++ ") "
    show (SComment s) = "; " ++ s
    show (SPat e) = " :pattern " ++ show e
    show (SOption x y) = ":" ++ x ++ " " ++ y

bitstringSort :: SExp
bitstringSort = SAtom "Bits"

bitstringListSort :: SExp
bitstringListSort = SAtom "BSList"

nameSort :: SExp
nameSort = SAtom "Name"

labelSort :: SExp
labelSort = SAtom "Label"

indexSort :: SExp
indexSort = SAtom "Index"

-- Data structure used by label checking

data CanonLabel = CanonAnd [CanonLabelBig]
    deriving (Show, Generic, Typeable)

data CanonLabelBig = 
    CanonBig (Bind [IdxVar] CanonAtom) 
      | CanonNoBig CanonAtom
    deriving (Show, Generic, Typeable)

data CanonAtom = 
    CanonLName NameExp
      | CanonZero
      | CanonAdv
      | CanonConst LblConst
    deriving (Show, Generic, Typeable)

instance Alpha CanonLabel
instance Subst Idx CanonLabel
instance Subst AExpr CanonLabel

instance Alpha CanonLabelBig
instance Subst Idx CanonLabelBig
instance Subst AExpr CanonLabelBig

instance Alpha CanonAtom
instance Subst Idx CanonAtom
instance Subst AExpr CanonAtom


----


data SolverEnv = SolverEnv {
    _constants :: M.Map String SExp,
    _lengthConstants :: M.Map String SExp,
    _symIndexEnv :: M.Map IdxVar SExp,
    _symNameEnv :: M.Map String SExp,
    _symLabelVarEnv :: M.Map (AlphaOrd ResolvedPath) SExp,
    _labelVals :: M.Map (AlphaOrd CanonLabelBig) SExp, -- Only used by label checking
    _varVals :: M.Map DataVar SExp,
    _funcInterps :: M.Map String (SExp, Int),
    _smtLog :: [SExp],
    _trivialVC :: Bool,
    _freshSMTCtr :: Int
                 }

makeLenses ''SolverEnv

initSolverEnv = SolverEnv M.empty M.empty M.empty M.empty M.empty M.empty M.empty M.empty [] True 0

newtype Sym a = Sym {unSym :: ReaderT Env (StateT SolverEnv (ExceptT String IO)) a }
    deriving (Functor, Applicative, Monad, MonadReader Env, MonadState SolverEnv, MonadIO)

liftCheck :: Check a -> Sym a
liftCheck c = do
    e <- ask
    o <- liftIO $ runExceptT $ runReaderT (unCheck $ local (set tcScope TcGhost) c) e
    case o of 
      Left s -> Sym $ lift $ throwError $ "SMT ERROR" 
      Right i -> return i



class SmtName a where
    smtName :: a -> Sym String

instance SmtName ResolvedPath where
    smtName p = do
        p' <- liftCheck $ normResolvedPath p
        return $ go p'
        where
            go :: ResolvedPath -> String
            go (PDot PTop a) = a 
            go PTop = "Top"
            go (PPathVar _ x) = show x
            go (PDot a b) = go a ++ "__" ++ b

instance SmtName Path where
    smtName (PRes p) = smtName p
    smtName r@_ = error $ "smtName of unresolved path: " ++ show r

freshSMTName :: Sym String
freshSMTName = do
    freshSMTCtr += 1
    i <- use freshSMTCtr
    return $ "x" ++ show i

freshSMTIndexName :: Sym String
freshSMTIndexName = do
    freshSMTCtr += 1
    i <- use freshSMTCtr
    return $ "i" ++ show i

freshSMTVal :: Maybe String -> Sym SExp
freshSMTVal name = do
    x <- freshSMTName
    case name of
      Just n -> emitComment $ filter (\x -> x /= '\n') $ "Constant " ++ x ++ " = " ++ n
      Nothing -> return ()
    emit $ SApp [SAtom "declare-const", SAtom x, bitstringSort]
    return (SAtom x)

freshIndexVal :: String -> Sym SExp
freshIndexVal name = do
    x <- freshSMTIndexName
    emitComment $ filter (\x -> x /= '\n') $ "Index " ++ x ++ " = " ++ name
    emit $ SApp [SAtom "declare-const", SAtom x, indexSort]
    return $ SAtom x

freshLengthVar :: Maybe String -> Sym SExp
freshLengthVar name = do
    x <- freshSMTName
    case name of
      Just n -> emitComment $ "Length Constant " ++ x ++ " = " ++ n
      Nothing -> return ()
    emit $ SApp [SAtom "declare-const", SAtom x, SAtom "Int"]
    emitAssertion $ sNot $ sEq (SAtom x) (SAtom "0")
    return $ SAtom x

emit :: SExp -> Sym ()
emit e = smtLog %= (e : )

emitRaw :: String -> Sym ()
emitRaw e = smtLog %= ((SAtom e) :)

emitComment :: String -> Sym ()
emitComment s = emit (SComment s)

emitAssertion :: SExp -> Sym ()
emitAssertion e = emit (SApp [SAtom "assert", e])

emitToProve :: SExp -> Sym ()
emitToProve e = do
    trivialVC .= False
    emitAssertion $ sNot e

getSMTQuery :: Sym () -> Sym () -> Check (Maybe String) -- Returns Nothing if trivially true
getSMTQuery setup k = do
    env <- ask
    res <- liftIO $ runExceptT $ runStateT (runReaderT (unSym go) env) initSolverEnv
    case res of
      Left _ -> Check $ lift $ throwError env
      Right (_, e) -> do
          if e^.trivialVC then return Nothing else do
                prelude <- liftIO $ readFile "prelude.smt2"
                let query = prelude ++ "\n" ++ (intercalate "\n" $ map (filter (\x -> x /= '\n')) $ map show $ reverse $ (SApp [SAtom "check-sat"]) : e^.smtLog)
                return $ Just query
    where
        go = do
            setup
            k

queryZ3 :: IORef (M.Map Int Bool) -> String -> IO (Either String Bool)
queryZ3 mp q = do
    let hq = hash q 
    m <- readIORef mp
    case M.lookup hq m of
      Just res -> return $ Right res
      Nothing -> do 
          resp <- readProcessWithExitCode "z3" ["-smt2", "-in"] q
          case resp of
            (ExitSuccess, "unsat\n", _) -> do
                atomicModifyIORef' mp $ \m -> (M.insert hq True m, ())
                return (Right True)
            (ExitSuccess, _, _) -> do
                atomicModifyIORef' mp $ \m -> (M.insert hq False m, ())
                return $ Right False
            (_, err, _) -> do
                return (Left err)


fromSMT :: Sym () -> Sym () -> Check (Maybe String, Bool)
fromSMT setup k = do
    oq <- getSMTQuery setup k
    case oq of
      Nothing -> return (Nothing, True)
      Just q -> do 
          b <- view $ envFlags . fLogSMT
          fn <- if b then Just <$> logSMT q else return Nothing
          z3mp <- view smtCache
          resp <- liftIO $ queryZ3 z3mp q
          case resp of
            Right b -> return (fn, b)
            Left err -> typeError (ignore def) $ "Z3 error: " ++ err   
              
raceSMT :: Sym () -> Sym () -> Sym () -> Check (Maybe String, Maybe Bool) -- bool corresponds to which said unsat first
raceSMT setup k1 k2 = do
    oq1 <- getSMTQuery setup k1
    oq2 <- getSMTQuery setup k2
    case (oq1, oq2) of
      (Nothing, _) -> return (Nothing, Just False)
      (_, Nothing) -> return (Nothing, Just True)
      (Just q1, Just q2) -> do 
          b <- view $ envFlags . fLogSMT
          fn1 <- if b then Just <$> logSMT q1 else return Nothing
          fn2 <- if b then Just <$> logSMT q2 else return Nothing
          sem <- liftIO $ newEmptyMVar 
          z3mp <- view smtCache
          p1 <- liftIO $ forkIO $ do 
              resp <- queryZ3 z3mp q1 
              case resp of
                  Right True -> putMVar sem $ Just (fn1, False)
                  Right False -> putMVar sem Nothing
                  Left err -> error $ "Z3 error: " ++ err   
          p2 <- liftIO $ forkIO $ do 
              resp <- queryZ3 z3mp q2
              case resp of
                  Right True -> putMVar sem $ Just (fn2, True)
                  Right False -> putMVar sem Nothing 
                  Left err -> error $ "Z3 error: " ++ err   
          o1 <- liftIO $ takeMVar sem
          case o1 of
            Just (fn, b) -> do
                liftIO $ killThread p1
                liftIO $ killThread p2
                return (fn, Just b)                        
            Nothing -> do 
                o2 <- liftIO $ takeMVar sem
                liftIO $ killThread p1
                liftIO $ killThread p2
                case o2 of
                  Nothing -> return (Nothing, Nothing)
                  Just (fn, b) -> return (fn, Just b)



sAnd :: [SExp] -> SExp
sAnd xs = 
    if length xs > 0 then 
        SApp $ [SAtom "and"] ++ xs
    else sTrue

sAnd2 x y = sAnd [x, y]

sOr :: SExp -> SExp -> SExp
sOr x y = SApp [SAtom "or", x, y]

sTrue :: SExp
sTrue = SAtom "true"

sFalse :: SExp
sFalse = SAtom "false"

sEq :: SExp -> SExp -> SExp
sEq x y = SApp [SAtom "=", x, y]

sImpl :: SExp -> SExp -> SExp
sImpl x y = SApp [SAtom "implies", x, y]

sNot :: SExp -> SExp
sNot x = SApp [SAtom "not", x]

sNotIn :: SExp -> [SExp] -> SExp
sNotIn x [] = sTrue
sNotIn x (y:ys) = sAnd [sEq (SAtom "FALSE") (SApp [SAtom "eq", x, y]), sNotIn x ys]

sDistinct :: [SExp] -> SExp
sDistinct [] = sTrue
sDistinct (x:xs) = sAnd2 (sNotIn x xs) (sDistinct xs)

sApp :: SExp -> [SExp] -> SExp
sApp f vs = 
    if length vs == 0 then f else (SApp $ f : vs)

---- Helpers for logging 

logSMT :: String -> Check String
logSMT s = do
    f <- takeFileName <$> (view $ envFlags . fFilePath)
    liftIO $ createDirectoryIfMissing False ".owl-log"
    fn <- liftIO $ findGoodFileName f
    liftIO $ writeFile fn s
    return fn
        where
            findGoodFileName :: String -> IO String
            findGoodFileName s = go s 0

            go s i = do
                b <- doesFileExist $ ".owl-log" </> (s ++ show i ++ ".smt2")
                if b then go s (i+1)
                     else return $ ".owl-log" </> (s ++ show i ++ ".smt2")

symIndex :: Idx -> Sym SExp
symIndex (IVar ispan v) = do
    iEnv <- use symIndexEnv
    case M.lookup v iEnv of 
      Just i -> return i
      Nothing -> do
          indices <- view $ inScopeIndices
          liftCheck $ typeError ispan (show $ pretty "SMT ERROR: unknown index " <> pretty v <> pretty " under inScopeIndices " <> pretty (map fst indices))
            
getSymName :: NameExp -> Sym SExp
getSymName ne = 
    case ne^.val of
      BaseName (is1, is2) s -> do
        nEnv <- use symNameEnv
        sn <- smtName s
        case M.lookup sn nEnv of
          Nothing -> error $ "UNKNOWN SYM NAME: " ++ show s
          Just f -> do
              case (is1, is2) of
                ([], []) -> return f
                _ -> do
                    vs1 <- mapM symIndex is1
                    vs2 <- mapM symIndex is2
                    return $ SApp $ f : vs1 ++ vs2
      ROName s is i -> do
          nEnv <- use symNameEnv
          sn <- smtName s
          case M.lookup sn nEnv of
              Nothing -> error $ "UNKNOWN SYM RO NAME: " ++ show s
              Just f -> do
                  case is of
                    [] -> return $ SApp $ [f, SAtom (show i)]
                    _ -> do
                        vs <- mapM symIndex is
                        return $ SApp $ [f] ++ vs ++ [SAtom $ show i]
      PRFName ne s -> do
          n <- getSymName ne
          return $ SApp [SAtom "PRFName", n, SAtom $ "\"" ++ s ++ "\""]


sForall :: [(SExp, SExp)] -> SExp -> [SExp] -> SExp
sForall vs bdy pats = 
    case vs of
      [] -> bdy
      _ -> 
        let v_sorts = SApp $ map (\(x, y) -> SApp [x, y]) vs in 
        let bdy' = case pats of
                     [] -> SApp [SAtom "!", bdy] 
                     _ -> SApp [SAtom "!", bdy, SPat (SApp pats)] 
        in
        SApp [SAtom "forall", v_sorts, bdy']

sExists :: [(SExp, SExp)] -> SExp -> [SExp] -> SExp
sExists vs bdy pats = 
    case vs of
      [] -> bdy
      _ -> 
        let v_sorts = SApp $ map (\(x, y) -> SApp [x, y]) vs in 
        let bdy' = case pats of
                     [] -> SApp [SAtom "!", bdy] 
                     _ -> SApp [SAtom "!", bdy, SPat (SApp pats)] 
        in
        SApp [SAtom "exists", v_sorts, bdy']


sValue :: SExp -> SExp
sValue n = SApp [SAtom "ValueOf", n]

-- Construct name expression out of base name and index arguments
sBaseName :: SExp -> [SExp] -> SExp
sBaseName n is = 
    case is of
      [] -> n
      _ -> SApp $ n : is

sLblOf :: SExp -> SExp
sLblOf n = SApp [SAtom "LabelOf", n]

sROName :: SExp -> [SExp] -> SExp -> SExp
sROName n is i = 
    case is of
      [] -> SApp $ [n, i]
      _ -> SApp $ n : (is ++ [i])

sHashSelect :: SExp -> Int -> SExp
sHashSelect s i = SApp [SAtom "HashSelect", s, SAtom (show i)]


instance Pretty CanonLabel where
    pretty (CanonAnd cs) = 
        mconcat $ intersperse (pretty " /\\ ") (map pretty cs) 

instance Pretty CanonLabelBig where        
    pretty (CanonNoBig ca) = pretty ca
    pretty (CanonBig ia) = 
        let (is, a) = prettyBind ia in 
        pretty "/\\_" <> is <> pretty "(" <> a <> pretty ")"

instance Pretty CanonAtom where
    pretty (CanonLName a) = pretty (nameLbl a)
    pretty (CanonAdv) = pretty advLbl
    pretty (CanonZero) = pretty zeroLbl
