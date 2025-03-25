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
import qualified System.Process.Text as T
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
import Pretty
import TypingBase
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Unsafe
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import qualified Parse as P
import qualified Text.Parsec as P
import qualified Data.Text as T
import qualified Data.Text.IO as T


data SExp = 
    SAtom String
      | SApp [SExp]
      | SComment T.Text
      | SPat SExp
      | SQid String
      | SNamed String
      | SOption String String

renderSExp :: SExp -> T.Text
renderSExp (SAtom t) = T.pack t
renderSExp (SApp xs) = T.pack " (" <> mconcat (intersperse (T.pack " ") (map renderSExp xs)) <> T.pack ")"
renderSExp (SComment s) = T.pack "; " <> s
renderSExp (SPat s) = T.pack " :pattern " <> renderSExp s
renderSExp (SQid s) = T.pack " :qid " <> T.pack s
renderSExp (SNamed s) = T.pack " :named " <> T.pack s
renderSExp (SOption x y) = T.pack ":" <> T.pack x <> T.pack " " <> T.pack y

instance Show SExp where
    show e = show (renderSExp e)

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
    CanonBig (Bind ([IdxVar], [DataVar]) CanonAtom) 
    deriving (Show, Generic, Typeable)

data CanonAtom = 
    CanonLName NameExp
      | CanonZero
      | CanonAdv
      | CanonGhost
      | CanonTop
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
    _symLabelHook :: Label -> Sym SExp,
    _constants :: M.Map String SExp,
    _hexConstants :: M.Map String SExp,
    _symIndexEnv :: M.Map IdxVar SExp,
    _symLabelVarEnv :: M.Map (AlphaOrd ResolvedPath) SExp,
    _labelVals :: M.Map (AlphaOrd CanonLabelBig) SExp, -- Only used by label checking
    -- _kdfPermCounter :: M.Map (AlphaOrd NameType) SExp,
    _memoInterpretAExp :: M.Map (AlphaOrd AExpr) SExp,
    _memoInterpretProp :: M.Map (AlphaOrd Prop) SExp,
    _varVals :: M.Map DataVar SExp,
    _funcInterps :: M.Map String (SExp, Int),
    _predInterps :: M.Map String SExp,
    -- _inODHInterp :: Maybe SExp,
    _smtLog :: [SExp],
    _smtPreludeSetup :: T.Text,
    _trivialVC :: Bool,
    _freshSMTCtr :: Int
                 }
                                    
type Check = Check' SolverEnv

initSolverEnv_ hk = SolverEnv hk M.empty M.empty M.empty 
   -- M.empty 
   M.empty M.empty M.empty M.empty M.empty M.empty M.empty 
   -- Nothing 
    [] mempty True 0


newtype Sym a = Sym {unSym :: ReaderT (Env SolverEnv) (StateT SolverEnv (ExceptT String IO)) a }
    deriving (Functor, Applicative, Monad, MonadReader (Env SolverEnv), MonadState SolverEnv, MonadIO)

makeLenses ''SolverEnv

liftCheck :: Check a -> Sym a
liftCheck c = do
    e <- ask
    o <- liftIO $ runExceptT $ runReaderT (unCheck $ local (set tcScope $ TcGhost False) $ local (set inSMT True) c) e
    case o of 
      Left s -> Sym $ lift $ throwError $ "SMT ERROR" 
      Right i -> return i

liftCheckWrapped :: String -> Check a -> Sym a
liftCheckWrapped s k = do
    r <- liftCheck $ withLog0 s k
    return r


class SmtName a where
    smtName :: a -> Sym String

instance SmtName ResolvedPath where
    smtName p = do
        p' <- liftCheck $ normResolvedPath p
        return $ go p'
        where
            go :: ResolvedPath -> String
            go (PDot PTop a) = cleanSMTIdent a 
            go PTop = "Top"
            go (PPathVar _ x) = show x
            go (PDot a b) = go a ++ "__" ++ cleanSMTIdent b

instance SmtName Path where
    smtName (PRes p) = smtName p
    smtName r@_ = error $ "smtName of unresolved path: " ++ show r

cleanSMTIdent :: String -> String
cleanSMTIdent s = map go s
    where
        go '\'' = '^' 
        go c = c

getFreshCtr :: Sym Int
getFreshCtr = do
    freshSMTCtr += 1
    use freshSMTCtr
        
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
      Just n -> emitComment $ T.pack $ filter (\x -> x /= '\n') $ "Constant " ++ x ++ " = " ++ n
      Nothing -> return ()
    emit $ SApp [SAtom "declare-const", SAtom x, bitstringSort]
    return (SAtom x)

freshIndexVal :: String -> Sym SExp
freshIndexVal name = do
    x <- freshSMTIndexName
    emitComment $ T.pack $ filter (\x -> x /= '\n') $ "Index " ++ x ++ " = " ++ name
    emit $ SApp [SAtom "declare-const", SAtom x, indexSort]
    return $ SAtom x

freshLengthVar :: Maybe String -> Sym SExp
freshLengthVar name = do
    x <- freshSMTName
    case name of
      Just n -> emitComment $ T.pack $ "Length Constant " ++ x ++ " = " ++ n
      Nothing -> return ()
    emit $ SApp [SAtom "declare-const", SAtom x, SAtom "Int"]
    emitAssertion $ sNot $ sEq (SAtom x) (SAtom "0")
    return $ SAtom x

emit :: SExp -> Sym ()
emit e = smtLog %= (e : )

emitRaw :: String -> Sym ()
emitRaw e = smtLog %= ((SAtom e) :)

emitComment :: T.Text -> Sym ()
emitComment s = emit (SComment $ s)

emitAssertion :: SExp -> Sym ()
emitAssertion e = do
    i <- freshSMTName
    emit (SApp [SAtom "assert", SApp [SAtom "!", e, SNamed i]])

emitToProve :: SExp -> Sym ()
emitToProve e = do
    trivialVC .= False
    emitAssertion $ sNot e

mkPred :: Path -> Sym SExp  
mkPred pth@(PRes (PDot p s)) = do
    pis <- use predInterps
    sn <- smtName pth
    case M.lookup sn pis of
      Just v -> return v
      Nothing ->  do
          md <- liftCheck $ openModule p
          case lookup s (md^.predicates) of
            Nothing -> error $ "Predicate " ++ show pth ++ " not found. " 
            Just b -> do
                ((ixs, xs), pr) <- liftCheck $ unbind b
                let ivs = map (\i -> (SAtom (show i), indexSort)) ixs
                let xvs = map (\x -> (SAtom (show x), bitstringSort)) xs
                withSMTIndices (map (\i -> (i, IdxGhost)) ixs) $ 
                    withSMTVars xs $ do
                        v <- interpretProp pr
                        emit $ SApp [SAtom "declare-fun", SAtom sn, SApp (replicate (length ixs) indexSort ++ replicate (length xs) bitstringSort), SAtom "Bool"]
                        let ax = sForall
                                    (ivs ++ xvs)
                                    (SApp [SAtom "=", sApp (SAtom sn : (map fst ivs) ++ (map fst xvs)), v])
                                    [sApp (SAtom sn : (map fst ivs) ++ (map fst xvs))]
                                    ("predDef_" ++ sn)
                        emitAssertion $ ax
                        return ()
                predInterps %= (M.insert sn (SAtom sn))
                return $ SAtom sn

-- symInODHProp :: Sym SExp
-- symInODHProp = do
--     o <- use inODHInterp 
--     case o of
--       Just v -> return v
--       Nothing -> do
--           x1 <- freshSMTName
--           x2 <- freshSMTName
--           x3 <- freshSMTName
--           withSMTVars [s2n x1, s2n x2, s2n x3] $ do
--               p <- liftCheck $ inODHProp (aeVar' $ s2n x1) (aeVar' $ s2n x2) (aeVar' $ s2n x3)
--               v <- interpretProp p
--               emitRaw $ "(declare-fun %inODHProp (Bits Bits Bits) Bool)"
--               let ax = sForall 
--                          [(SAtom x1, bitstringSort), (SAtom x2, bitstringSort), (SAtom x3, bitstringSort)]
--                          (SApp [SAtom "=", sApp [SAtom "%inODHProp", SAtom x1, SAtom x2, SAtom x3], v])
--                          [sApp [SAtom "%inODHProp", SAtom x1, SAtom x2, SAtom x3]]
--                          ("inODHDef")
--               emitAssertion ax
--               return $ SAtom "%inODHProp"
--               assign inODHInterp $ Just $ SAtom "%inODHProp"
--               return $ SAtom "%inODHProp"

renderSMTLog :: [SExp] -> T.Text
renderSMTLog exps = 
    mconcat $ intersperse (T.pack "\n") $ map (T.map (\c -> if c == '\n' then ' ' else c)) $ map renderSExp $ reverse exps

getSMTQuery :: SolverEnv -> Sym () -> Sym () -> Check (Maybe T.Text) -- Returns Nothing if trivially true
getSMTQuery senv setup k = do
    env <- ask
    res <- liftIO $ runExceptT $ runStateT (runReaderT (unSym go) env) senv
    case res of
      Left _ -> Check $ lift $ throwError env
      Right (_, e) -> do
          if e^.trivialVC then return Nothing else do
                let prelude = e^.smtPreludeSetup
                let query = prelude <> (renderSMTLog $ (SApp [SAtom "check-sat"]) : e^.smtLog)
                return $ Just query
    where
        go = do
            setup
            k

trimnl :: String -> String
trimnl = reverse . dropWhile (=='\n') . reverse

wrapLogIO :: String -> IO a -> IO a
wrapLogIO s k = do
    putStrLn $ "begin " ++ s
    r <- k
    putStrLn $ "end " ++ s
    return r


queryZ3 :: Bool -> String -> IORef (Map String P.Z3Result) -> IORef (M.Map Int Bool) -> T.Text -> IO (Either String (Bool, Maybe String))
queryZ3 logsmt filepath z3results mp q = do
    let hq = hash q 
    m <- readIORef mp
    case M.lookup hq m of
      Just res -> return $ Right (res, Nothing)
      Nothing -> do 
          ofn  <- case logsmt of
                    False -> return Nothing
                    True -> do
                        b <- logSMT filepath q
                        return $ Just b
          resp <- readProcessWithExitCode "z3" ["-smt2", "-st", "-in"] $ T.unpack q
          case resp of
            (ExitSuccess, s, _) -> do                           
              pres <- P.runParserT P.parseZ3Result () "" $ s
              case pres of
                Left err -> do
                    putStrLn $ "Z3 parse error on " ++ s
                    putStrLn $ T.unpack q
                    return $ Left $ "Z3 ERROR: " ++ show err
                Right z3result -> do
                    case ofn of
                      Nothing -> return ()
                      Just b -> modifyIORef z3results ((b, z3result) :)
                    when (P._isUnsat z3result) $ do 
                        atomicModifyIORef' mp $ \m -> (M.insert hq True m, ())
                    return $ Right (P._isUnsat z3result, ofn)
            (_, err, _) -> return (Left err)

fromSMT :: SolverEnv -> String -> Sym () -> Sym () -> Check (Maybe String, Bool)
fromSMT senv s setup k = pushRoutine ("fromSMT: " ++ s) $ do
    oq <- getSMTQuery senv setup k
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
            Left err -> typeError $ "Z3 error: " ++ err   

              
raceSMT :: SolverEnv -> Sym () -> Sym () -> Sym () -> Check (Maybe String, Maybe Bool) -- bool corresponds to which said unsat first
raceSMT senv setup k1 k2 = do
    oq1 <- getSMTQuery senv setup k1
    oq2 <- getSMTQuery senv setup k2
    res <- case (oq1, oq2) of
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
                  Left err -> do
                      b <- logSMT filepath q1
                      error $ "Z3 error: " ++ err ++ " logged to " ++ b
          p2 <- liftIO $ forkIO $ do 
              resp <- queryZ3 logsmt filepath z3rs z3mp q2
              case resp of
                  Right (True, fn) -> putMVar sem $ Just (fn, True)
                  Right (False, _) -> putMVar sem Nothing 
                  Left err -> do
                      b <- logSMT filepath q2 
                      error $ "Z3 error: " ++ err ++ " logged to " ++ b
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
    return res



-- Smart app
sApp :: [SExp] -> SExp
sApp [x] = x
sApp xs = SApp xs

sInt :: Int -> SExp
sInt i = SAtom $ show i

sAnd :: [SExp] -> SExp
sAnd []  = sTrue
sAnd [x] = x
sAnd xs = SApp $ [SAtom "and"] ++ xs

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

allPairs :: [a] -> [(a, a)]
allPairs l = [(x,y) | (x:ys) <- tails l, y <- ys]

sAtMostOne :: [SExp] -> SExp
sAtMostOne xs = sAnd $ map (\(x, y) -> sNot $ sAnd2 x y) $ allPairs xs  

makeHex :: String -> Sym SExp
makeHex s = do
    liftCheck $ assert  "makeHex: string length must be even" (length s `mod` 2 == 0)
    hc <- use hexConstants
    if M.member s hc then
        return $ hc M.! s
    else do
        let len = case length s of
                         0 -> 0
                         _ -> (length s) `quot` 2
        let s' = "%hc_" ++ s
        emit $ SApp [SAtom "declare-const", SAtom s', SAtom "Bits"]
        emitAssertion $ sEq (sLength (SAtom s')) (SApp [SAtom "I2B", SAtom $ show len])
        emitAssertion $ SApp [SAtom "IsConstant", SAtom s']
        emitAssertion $ SApp [SAtom "HasHex", SAtom s', SAtom $ "\"" ++ s ++ "\""]
        hexConstants %= (M.insert s (SAtom s'))
        return $ SAtom s'

getFunc :: String -> Sym SExp
getFunc s = do
    fs <- use funcInterps
    case M.lookup s fs of
      Just (v, _) -> return v
      Nothing -> error $ "Function not in SMT: " ++ show s ++ show (M.keys fs)

getTopLevelFunc s = do
    sn <- smtName $ topLevelPath s
    getFunc sn

lengthConstant :: String -> SExp
lengthConstant s = 
    case s of
      "expandkey" -> SApp [SAtom "NameKindLength", SAtom "Expandkey"]
      "extractkey" -> SApp [SAtom "NameKindLength", SAtom "Extractkey"]
      "nonce" -> SAtom "NonceLength"
      "DH" -> SApp [SAtom "NameKindLength", SAtom "DHkey"]
      "enckey" ->  SApp [SAtom "NameKindLength", SAtom "Enckey"]
      "pke_sk" ->  SApp [SAtom "NameKindLength", SAtom "PKEkey"]
      "sigkey" ->  SApp [SAtom "NameKindLength", SAtom "Sigkey"]
      -- "kdfkey" ->  SApp [SAtom "NameKindLength", SAtom "KDFkey"]
      "mackey" ->  SApp [SAtom "NameKindLength", SAtom "MACkey"]
      "signature" -> SAtom "SignatureLen"
      "group" -> SAtom "GroupLen"
      "vk" -> SAtom "VKLen"
      "pke_pk" -> SAtom "PKEPubLen"
      "maclen" -> SAtom "MAClen"
      "tag" -> SAtom "Taglen"
      "counter" -> SAtom "Counterlen"
      "crh" -> SAtom "CrhLength"

symLenConst :: String -> Sym SExp
symLenConst s = do
    let v = lengthConstant s
    return $ SApp [SAtom "I2B", v]

sLength :: SExp -> SExp
sLength e = SApp [SAtom "length", e]

bTrue :: SExp
bTrue = SAtom "TRUE"

bFalse :: SExp
bFalse = SAtom "FALSE"

unit :: SExp
unit = SAtom "UNIT"

withAExpMemo :: (AExpr -> Sym SExp) -> AExpr -> Sym SExp 
withAExpMemo k a = do
    m <- use memoInterpretAExp
    case M.lookup (AlphaOrd a) m of
      Just v -> return v
      Nothing -> do
          v <- k a
          memoInterpretAExp %= (M.insert (AlphaOrd a) v)
          return v

interpretAExp :: AExpr -> Sym SExp
interpretAExp = withAExpMemo $ \ae' -> do
    ae <- liftCheck $ normalizeAExpr ae'
    case ae^.val of
      AEVar _ x -> do
        env <- use varVals
        case M.lookup x env of 
            Just v -> return v
            Nothing -> liftCheck $ typeError $ "SMT ERROR : Cannot find " ++ show x ++ " with varVals " ++ show (owlpretty (M.keys env))
      AEApp f _ xs -> do
        vs <- mapM interpretAExp xs
        case f of
          -- Special cases
          f | f `aeq` (topLevelPath "unit") -> return unit
          f | f `aeq` (topLevelPath "true") -> return bTrue
          f | f `aeq` (topLevelPath "false") -> return bFalse
          _ -> do
              vf <- getFunc =<< (smtName f)
              return $ sApp $ vf : vs
      AEHex s -> makeHex s
      AELenConst s -> symLenConst s
      AEInt i -> return $ SApp [SAtom "I2B", SAtom (show i)]
      AE_Extract a b -> do 
          va <- interpretAExp a
          vb <- interpretAExp b
          return $ SApp [SAtom "Extract", va, vb]
      AE_Expand a b nks j -> do 
          va <- interpretAExp a
          vb <- interpretAExp b
          nk_lengths <- liftCheck $ forM nks $ \nk -> sNameKindLength <$> smtNameKindOf nk
          let start = sPlus $ take j nk_lengths
          let segment = nk_lengths !! j
          return $ SApp [SAtom "Expand", va, vb, start, segment]
      --AEPreimage p ps as -> do
      --    aes <- liftCheck $ getROPreimage p ps as
      --    interpretAExp aes
      AEGet ne -> do
          symNameExp ne
      AEGetEncPK ne -> interpretAExp $ aeApp (topLevelPath  "enc_pk") [] [mkSpanned $ AEGet ne]
      AEGetVK ne -> interpretAExp $ aeApp (topLevelPath  "vk") [] [mkSpanned $ AEGet ne]

sName :: String -> [SExp] -> Sym SExp
sName n ivs = do
    let vn = SAtom $ "%name_" ++ n
    return $ sApp $ vn : ivs 

withSMTIndices :: [(IdxVar, IdxType)] -> Sym a -> Sym a
withSMTIndices xs k = do
    sIE <- use symIndexEnv
    symIndexEnv %= (M.union $ M.fromList $ map (\(i, _) -> (i, SAtom $ cleanSMTIdent $ show i)) xs) 
    res <- withIndices (map (\(x, t) -> (x, (ignore $ show x, t))) xs) k
    symIndexEnv .= sIE
    return res

withSMTVars :: [DataVar] -> Sym a -> Sym a
withSMTVars xs k = do
    vVs <- use varVals
    varVals %= (M.union $ M.fromList $ map (\v -> (v, SAtom $ cleanSMTIdent $ show v)) xs)
    let tyc = map (\v -> (v, (ignore $ show v, Nothing, tGhost))) xs 
    res <- withVars tyc $ k
    varVals .= vVs
    return res

withSMTVars' :: [(DataVar, SExp)] -> Sym a -> Sym a
withSMTVars' xs k = do
    vVs <- use varVals
    varVals %= (M.union $ M.fromList $ map (\(x, v) -> (x, v)) xs)
    let tyc = map (\(x, v) -> (x, (ignore $ show x, Nothing, tGhost))) xs 
    res <- withVars tyc $ k
    varVals .= vVs
    return res

withSMTVarsTys :: [(DataVar, Ty)] -> Sym a -> Sym a
withSMTVarsTys xs k = do
    vVs <- use varVals
    varVals %= (M.union $ M.fromList $ map (\(v, _) -> (v, SAtom $ show v)) xs)
    let tyc = map (\(v, t) -> (v, (ignore $ show v, Nothing, t))) xs 
    res <- withVars tyc $ k 
    varVals .= vVs
    return res

withQuantBinders :: [QuantBinder] -> Sym a -> Sym a
withQuantBinders [] m = m
withQuantBinders ((QIdx i):xs) m = withSMTIndices [(i, IdxGhost)] $ withQuantBinders xs m
withQuantBinders ((QBV x):xs) m = withSMTVars [x] $ withQuantBinders xs m

---- Helpers for logging 

logSMT :: String -> T.Text -> IO String
logSMT filepath q = do
    let f = takeFileName filepath
    createDirectoryIfMissing False ".owl-log"
    fn <- findGoodFileName f
    writeFile fn $ T.unpack q
    return fn
        where
            findGoodFileName :: String -> IO String
            findGoodFileName s = go s 0

            go s i = do
                b <- doesFileExist $ ".owl-log" </> (s ++ show i ++ ".smt2")
                if b then go s (i+1)
                     else return $ ".owl-log" </> (s ++ show i ++ ".smt2")

symIndex :: Idx -> Sym SExp
symIndex idx@(IVar ispan iname v) = do
    iEnv <- use symIndexEnv
    case M.lookup v iEnv of 
      Just i -> return i
      Nothing -> do
          indices <- view $ inScopeIndices
          liftIO $ putStrLn $ "Unknown index: " ++ show (unignore iname)
          liftCheck $ typeError (show $ owlpretty "SMT ERROR: unknown index " <> owlpretty iname <> owlpretty " under inScopeIndices " <> (list $ map (owlpretty . fst) indices) <> owlpretty " and iEnv " <> (list $ map (owlpretty . fst) $ M.toList iEnv))

data SMTNameDef = 
    SMTBaseName (SExp, ResolvedPath) (Bind ([IdxVar], [IdxVar]) (Maybe NameType))

withSMTNameDef :: SMTNameDef -> ((SExp, ResolvedPath) -> (([IdxVar], [IdxVar])) 
                -> Maybe NameType -> Sym a) -> Sym a                      
withSMTNameDef df k = do
    case df of
      SMTBaseName p b -> do
          (idxs, ont) <- liftCheck $ unbind b
          k p (idxs) ont

flattenNameDefs :: Map ResolvedPath (Bind ([IdxVar], [IdxVar]) NameDef) ->
                   Sym [SMTNameDef]
flattenNameDefs xs = do
    ys <- forM xs $ \(n, b) -> do
        ((is, ps), nd) <- liftCheck $ unbind b
        case nd of
          BaseDef (nt, _) -> do
              sn <- smtName n
              return [SMTBaseName ((SAtom $ "%name_" ++ sn), n) (bind (is, ps) (Just nt))] 
          AbstractName -> do
              sn <- smtName n
              return [SMTBaseName ((SAtom $ "%name_" ++ sn), n) (bind (is, ps) Nothing)]
          AbbrevNameDef _ -> return []
    return $ concat ys
            
sPlus :: [SExp] -> SExp
sPlus [] = SAtom "0"
sPlus xs = SApp $ (SAtom "+") : xs

sNameKindLength :: SExp -> SExp
sNameKindLength n = SApp [SAtom "NameKindLength", n]

getExpandArgs :: SMTNameKindOf a => AExpr -> AExpr -> [a] -> Int -> Sym (SExp, SExp, SExp, SExp)
getExpandArgs a b nks j = do
    va <- interpretAExp a
    vb <- interpretAExp b
    nk_lengths <- liftCheck $ forM nks $ \nk -> sNameKindLength <$> smtNameKindOf nk
    let start = sPlus $ take j nk_lengths
    let segment = nk_lengths !! j
    return (va, vb, start, segment)

getSymName :: NameExp -> Sym SExp
getSymName ne = do 
    ne' <- liftCheck $ normalizeNameExp ne
    case ne'^.val of
      NameConst (is1, is2) s [] -> do
        sn <- smtName s
        vs1 <- mapM symIndex is1
        vs2 <- mapM symIndex is2
        sName sn (vs1 ++ vs2) 
      ExtractName a b nt _ -> do
          va <- interpretAExp a
          vb <- interpretAExp b
          return $ SApp [SAtom "ExtractName", va, vb]
      ExpandName a b nks j nt _ -> do
          va <- interpretAExp a
          vb <- interpretAExp b
          nk_lengths <- liftCheck $ forM nks $ \nk -> sNameKindLength <$> smtNameKindOf nk
          let start = sPlus $ take j nk_lengths
          let segment = nk_lengths !! j
          return $ SApp [SAtom "ExpandName", va, vb, start, segment]

symNameExp :: NameExp -> Sym SExp
symNameExp ne = do
    n <- getSymName ne
    return $ SApp [SAtom "ValueOf", n]

sForall :: [(SExp, SExp)] -> SExp -> [SExp] -> String -> SExp
sForall vs bdy pats qid = 
    case vs of
      [] -> bdy
      _ -> 
        let v_sorts = SApp $ map (\(x, y) -> SApp [x, y]) vs in 
        let bdy' = case pats of
                     [] -> SApp [SAtom "!", bdy, SQid qid] 
                     _ -> SApp [SAtom "!", bdy, SPat (sApp pats), SQid qid] 
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
                     _ -> SApp [SAtom "!", bdy, SPat (sApp pats), SQid qid] 
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

mkSList :: String -> [SExp] -> SExp
mkSList sort [] = SApp [SAtom "as", SAtom "nil", SAtom ("(List " ++ sort ++")")]
mkSList sort (x:xs) = SApp [SAtom "insert", x, mkSList sort xs]

withPropMemo :: (Prop -> Sym SExp) -> Prop -> Sym SExp 
withPropMemo k a = do
    m <- use memoInterpretProp
    case M.lookup (AlphaOrd a) m of
      Just v -> return v
      Nothing -> do
          v <- k a
          memoInterpretProp %= (M.insert (AlphaOrd a) v)
          return v

interpretProp :: Prop -> Sym SExp
interpretProp = withPropMemo $ \p -> do
    case p^.val of
      PTrue -> return sTrue
      PFalse -> return sFalse
      (PAnd p1 p2) -> 
        liftM2 (sAnd2) (interpretProp p1) (interpretProp p2)
      (POr p1 p2) ->
        liftM2 (sOr) (interpretProp p1) (interpretProp p2)
      (PImpl p1 p2) ->
        liftM2 (sImpl) (interpretProp p1) (interpretProp p2)
      (PNot p) ->
        sNot <$> interpretProp p
      PLetIn a xp -> do
          (x, p) <- liftCheck $ unbind xp
          interpretProp $ subst x a p
      PApp s is ps -> do 
          vs <- mkPred s 
          ixs <- mapM symIndex is
          vps <- mapM interpretAExp ps
          return $ sApp (vs : ixs ++ vps)
      PAADOf ne a -> do
          p <- liftCheck $ extractAAD ne a
          interpretProp p
      -- PInODH s ikm info -> do
      --     pv <- symInODHProp
      --     v1 <- interpretAExp s
      --     v2 <- interpretAExp ikm
      --     v3 <- interpretAExp info
      --     return $ sApp [pv, v1, v2, v3]
      (PEq p1 p2) -> do
          v1 <- interpretAExp p1
          v2 <- interpretAExp p2
          return $ SApp [SAtom "=", SAtom "TRUE", SApp [SAtom "eq", v1, v2]]
      (PEqIdx i1 i2) ->
        liftM2 (sEq) (symIndex i1) (symIndex i2)
      (PIsConstant a) -> do
          v <- interpretAExp a
          return $ SApp [SAtom "IsConstant", v]
      (PQuant q _ ip) -> do
          (xs, (trigger, p)) <- liftCheck $ unbind ip
          v <- withQuantBinders xs $ interpretProp p
          trig <- case trigger of
                    Just trigger -> do
                        trig <- withQuantBinders xs $ interpretAExp trigger
                        return [trig]
                    Nothing -> return []
          let smtBinders :: [QuantBinder] -> [(SExp, SExp)]
              smtBinders [] = []
              smtBinders ((QIdx i):xs) = (SAtom $ cleanSMTIdent $ show i, indexSort) : smtBinders xs
              smtBinders ((QBV x):xs) = (SAtom $ cleanSMTIdent $ show x, bitstringSort) : smtBinders xs

          case q of
            Forall -> return $ sForall (smtBinders xs) v trig $ "anon_forall"
            Exists -> return $ sExists (smtBinders xs) v trig $ "anon_exists"
      (PHonestPKEnc ne a) -> do
          vn <- getSymName ne
          a' <- interpretAExp a
          return $ SApp $ [SAtom "HonestPKEnc", vn, a']
      (PHappened s (id1, id2) xs) -> do
          vs <- mapM interpretAExp xs
          ivs <- mapM symIndex id1
          ivs' <- mapM symIndex id2
          sn <- smtName s
          return $ SApp $ [SAtom "Happened", SAtom ("\"" ++ sn ++ "\""), mkSList "Index" (ivs ++ ivs'), mkSList "Bits" vs]
      (PFlow l1 l2 ) -> do
        slh <- use symLabelHook
        x <- slh l1
        y <- slh l2
        return $ SApp [SAtom "Flows", x, y]

instance OwlPretty CanonLabel where
    owlpretty (CanonAnd cs) = 
        mconcat $ intersperse (owlpretty " /\\ ") (map owlpretty cs) 

instance OwlPretty CanonLabelBig where        
    owlpretty (CanonBig xia) = 
        let ((is, xs), a) = unsafeUnbind xia in 
        let b1 = case is of
                   [] -> mempty
                   _ -> owlpretty "/\\_" <> owlpretty is
        in
        let b2 = case xs of 
                   [] -> mempty
                   _ -> owlpretty "/\\_" <> owlpretty xs
        in
        let p = if length is + length xs > 0 then (owlpretty "(" <> owlpretty a <> owlpretty  ")") else owlpretty a
        in
        b1 <> b2 <> p 

instance OwlPretty CanonAtom where
    owlpretty (CanonLName a) = owlpretty (nameLbl a)
    owlpretty (CanonAdv) = owlpretty advLbl
    owlpretty (CanonTop) = owlpretty topLbl
    owlpretty (CanonGhost) = owlpretty ghostLbl
    owlpretty (CanonZero) = owlpretty zeroLbl


class SMTNameKindOf a where
    smtNameKindOf :: a -> Check SExp

instance SMTNameKindOf NameType where
    smtNameKindOf nt = 
        case nt^.val of
          NT_DH -> return $ SAtom "DHkey"
          NT_Enc _ -> return $ SAtom "Enckey"
          NT_StAEAD _ _ _ _ -> return $ SAtom "Enckey"
          NT_PKE _ -> return $ SAtom "PKEkey"
          NT_Sig _ -> return $ SAtom "Sigkey"
          NT_ExpandKey _ -> return $ SAtom "Expandkey"
          NT_ExtractKey _ -> return $ SAtom "Extractkey"
          -- NT_KDF _ _ -> return $ SAtom "KDFkey"
          NT_MAC _ -> return $ SAtom "MACkey"
          NT_Nonce l -> do
              let v = lengthConstant l 
              return $ SApp [SAtom "Nonce", v]
          NT_App p ps as -> resolveNameTypeApp False p ps as >>= smtNameKindOf

instance SMTNameKindOf NameKind where
    smtNameKindOf nk = 
        case nk of
          NK_DH ->    return $ SAtom "DHkey"
          NK_Enc ->   return $ SAtom "Enckey"
          NK_ExpandKey ->   return $ SAtom "Expandkey"
          NK_ExtractKey ->   return $ SAtom "Extractkey"
          NK_PKE ->   return $ SAtom "PKEkey" 
          NK_Sig ->   return $ SAtom "Sigkey"
          NK_MAC ->   return $ SAtom "MACkey"
          NK_Nonce l -> do
              let v = lengthConstant l 
              return $ SApp [SAtom "Nonce", v] 
