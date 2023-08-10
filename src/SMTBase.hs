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
import Data.Time.Clock
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
import Unbound.Generics.LocallyNameless.Unsafe
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import qualified Parse as P
import qualified Text.Parsec as P

data SExp = 
    SAtom String
      | SApp [SExp]
      | SComment String
      | SPat SExp
      | SQid String
      | SOption String String 

instance Show SExp where
    show (SAtom s) = s
    show (SApp xs) = " (" ++ intercalate " " (map show xs) ++ ") "
    show (SComment s) = "; " ++ s
    show (SPat e) = " :pattern " ++ show e
    show (SQid s) = " :qid " ++ s
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
    _symLabelVarEnv :: M.Map (AlphaOrd ResolvedPath) SExp,
    _labelVals :: M.Map (AlphaOrd CanonLabelBig) SExp, -- Only used by label checking
    _varVals :: M.Map DataVar SExp,
    _funcInterps :: M.Map String (SExp, Int),
    _smtLog :: [SExp],
    _trivialVC :: Bool,
    _freshSMTCtr :: Int
                 }

makeLenses ''SolverEnv

initSolverEnv = SolverEnv M.empty M.empty M.empty M.empty M.empty M.empty M.empty [] True 0

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

trimnl :: String -> String
trimnl = reverse . dropWhile (=='\n') . reverse

queryZ3 :: Bool -> String -> IORef [P.Z3Result] -> IORef (M.Map Int Bool) -> String -> IO (Either String (Bool, Maybe String))
queryZ3 logsmt filepath z3results mp q = do
    let hq = hash q 
    m <- readIORef mp
    case M.lookup hq m of
      Just res -> return $ Right (res, Nothing)
      Nothing -> do 
          t0 <- getCurrentTime
          resp <- readProcessWithExitCode "z3" ["-smt2", "-st", "-in"] q
          case resp of
            (ExitSuccess, s, _) -> do                           
              pres <- P.runParserT P.parseZ3Result () "" s
              case pres of
                Left err -> do
                    putStrLn $ "Z3 parse error on " ++ s
                    return $ Left $ "Z3 ERROR: " ++ show err
                Right z3result -> do
                    fn <- case logsmt of
                            False -> return Nothing
                            True -> do
                              modifyIORef z3results (z3result :)
                              t1 <- getCurrentTime
                              let resultAnn = "; Result: " ++ (if P._isUnsat z3result then "unsat" else "unknown")
                              let timeAnn = "; Query time: " ++ show (diffUTCTime t1 t0)
                              let rlimitAnn = "; Rlimit: " ++ show (P._rlimitCount z3result)
                              let ann = resultAnn ++ "\n" ++ timeAnn ++ "\n" ++ rlimitAnn ++ "\n"
                              b <- logSMT filepath $ ann ++ q
                              return $ Just b
                    atomicModifyIORef' mp $ \m -> (M.insert hq (P._isUnsat z3result) m, ())
                    return $ Right (P._isUnsat z3result, fn)
            (_, err, _) -> return (Left err)

fromSMT :: Sym () -> Sym () -> Check (Maybe String, Bool)
fromSMT setup k = do
    oq <- getSMTQuery setup k
    case oq of
      Nothing -> return (Nothing, True)
      Just q -> do 
          logsmt <- view $ envFlags . fLogSMT
          filepath <- view $ envFlags . fFilePath
          z3mp <- view smtCache
          z3rs <- view z3Results
          resp <- liftIO $ queryZ3 logsmt filepath z3rs z3mp q
          case resp of
            Right (b, fn) -> return (fn, b)
            Left err -> typeError (ignore def) $ "Z3 error: " ++ err   
              
raceSMT :: Sym () -> Sym () -> Sym () -> Check (Maybe String, Maybe Bool) -- bool corresponds to which said unsat first
raceSMT setup k1 k2 = do
    oq1 <- getSMTQuery setup k1
    oq2 <- getSMTQuery setup k2
    case (oq1, oq2) of
      (Nothing, _) -> return (Nothing, Just False)
      (_, Nothing) -> return (Nothing, Just True)
      (Just q1, Just q2) -> do 
          sem <- liftIO $ newEmptyMVar 
          z3mp <- view smtCache
          logsmt <- view $ envFlags . fLogSMT
          filepath <- view $ envFlags . fFilePath
          z3rs <- view z3Results
          p1 <- liftIO $ forkIO $ do 
              resp <- queryZ3 logsmt filepath z3rs z3mp q1 
              case resp of
                  Right (True, fn) -> putMVar sem $ Just (fn, False)
                  Right (False, _) -> putMVar sem Nothing
                  Left err -> error $ "Z3 error: " ++ err   
          p2 <- liftIO $ forkIO $ do 
              resp <- queryZ3 logsmt filepath z3rs z3mp q2
              case resp of
                  Right (True, fn) -> putMVar sem $ Just (fn, True)
                  Right (False, _) -> putMVar sem Nothing 
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



-- Smart app
sApp :: [SExp] -> SExp
sApp [x] = x
sApp [] = error "Empty sApp"
sApp xs = SApp xs

sInt :: Int -> SExp
sInt i = SAtom $ show i

sAnd :: [SExp] -> SExp
sAnd xs = 
    if length xs > 0 then 
        SApp $ [SAtom "and"] ++ xs
    else sTrue

sAnd2 x y = sAnd [x, y]

sOr :: SExp -> SExp -> SExp
sOr x y = SApp [SAtom "or", x, y]

sOrs :: [SExp] -> SExp
sOrs xs = SApp $ [SAtom "or"] ++ xs

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

sName :: Bool -> String -> [SExp] -> Maybe Int -> SExp
sName isRO n ivs oi = 
    let vn = case oi of
               Nothing -> if isRO then (SAtom $ "%name_" ++ n ++ "_0") else (SAtom $ "%name_" ++ n)
               Just i -> SAtom $ "%name_" ++ n ++ "_" ++ (show i)
    in
    sApp $ vn : ivs 

withIndices :: [(IdxVar, IdxType)] -> Sym a -> Sym a
withIndices xs k = do
    sIE <- use symIndexEnv
    symIndexEnv %= (M.union $ M.fromList $ map (\(i, _) -> (i, SAtom $ show i)) xs) 
    res <- local (over inScopeIndices $ (++) xs) k
    symIndexEnv .= sIE
    return res

---- Helpers for logging 

logSMT :: String -> String -> IO String
logSMT filepath q = do
    let f = takeFileName filepath
    createDirectoryIfMissing False ".owl-log"
    fn <- findGoodFileName f
    writeFile fn q
    return fn
        where
            findGoodFileName :: String -> IO String
            findGoodFileName s = go s 0

            go s i = do
                b <- doesFileExist $ ".owl-log" </> (s ++ show i ++ ".smt2")
                if b then go s (i+1)
                     else return $ ".owl-log" </> (s ++ show i ++ ".smt2")

symIndex :: Idx -> Sym SExp
symIndex idx@(IVar ispan v) = do
    iEnv <- use symIndexEnv
    case M.lookup v iEnv of 
      Just i -> return i
      Nothing -> do
          indices <- view $ inScopeIndices
          liftIO $ putStrLn $ "Unknown index: " ++ show v
          liftCheck $ typeError ispan (show $ pretty "SMT ERROR: unknown index " <> pretty v <> pretty " under inScopeIndices " <> pretty (map fst indices))

flattenNameDefs :: Map ResolvedPath (Bind ([IdxVar], [IdxVar]) NameDef) ->
                   Sym (Map (ResolvedPath, Maybe Int) (Bind ([IdxVar], [IdxVar]) NameDef))
flattenNameDefs xs = do
    ys <- forM xs $ \(n, b) -> do
        ((is, ps), nd) <- liftCheck $ unbind b
        case nd of
          BaseDef _ -> return [((n, Nothing), b)]
          AbstractName -> return [((n, Nothing), b)]
          RODef (as, nts) ->
              return $ map (\i -> ((n, Just i), bind (is, ps) $ RODef (as, [nts !! i]))) [0 .. (length nts - 1)]
    return $ concat ys

smtNameOfFlattenedName :: (ResolvedPath, Maybe Int) -> Sym SExp
smtNameOfFlattenedName (n, oi) = do
    sn <- smtName n
    case oi of
      Nothing -> return $ SAtom $ "%name_" ++ sn
      Just i -> return $ SAtom $ "%name_" ++ sn ++ "_" ++ (show i)

            
getSymName :: NameExp -> Sym SExp
getSymName ne = do 
    liftCheck $ debug $ pretty "getSymName" <+> pretty ne
    ne' <- liftCheck $ normalizeNameExp ne
    case ne'^.val of
      NameConst (is1, is2) s oi -> do
        sn <- smtName s
        vs1 <- mapM symIndex is1
        vs2 <- mapM symIndex is2
        isRO <- liftCheck $ isNameDefRO s
        return $ sName isRO sn (vs1 ++ vs2) oi
      PRFName ne1 s -> do
          n <- getSymName ne1
          return $ SApp [SAtom "PRFName", n, SAtom $ "\"" ++ s ++ "\""]


sForall :: [(SExp, SExp)] -> SExp -> [SExp] -> String -> SExp
sForall vs bdy pats qid = 
    case vs of
      [] -> bdy
      _ -> 
        let v_sorts = SApp $ map (\(x, y) -> SApp [x, y]) vs in 
        let bdy' = case pats of
                     [] -> SApp [SAtom "!", bdy, SQid qid] 
                     _ -> SApp [SAtom "!", bdy, SPat (SApp pats), SQid qid] 
        in
        SApp [SAtom "forall", v_sorts, bdy']

sExists :: [(SExp, SExp)] -> SExp -> [SExp] -> String -> SExp
sExists vs bdy pats qid = 
    case vs of
      [] -> bdy
      _ -> 
        let v_sorts = SApp $ map (\(x, y) -> SApp [x, y]) vs in 
        let bdy' = case pats of
                     [] -> SApp [SAtom "!", bdy, SQid qid] 
                     _ -> SApp [SAtom "!", bdy, SPat (SApp pats), SQid qid] 
        in
        SApp [SAtom "exists", v_sorts, bdy']


sValue :: SExp -> SExp
sValue n = SApp [SAtom "ValueOf", n]

sLblOf :: SExp -> SExp
sLblOf n = SApp [SAtom "LabelOf", n]

sROName :: SExp -> [SExp] -> SExp -> SExp
sROName n is i =
    case is of
      [] -> SApp $ [n, i]
      _ -> SApp $ n : (is ++ [i])

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
