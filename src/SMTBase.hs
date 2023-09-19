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
import Pretty
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
      | SNamed String
      | SOption String String 

instance Show SExp where
    show (SAtom s) = s
    show (SApp xs) = " (" ++ intercalate " " (map show xs) ++ ") "
    show (SComment s) = "; " ++ s
    show (SPat e) = " :pattern " ++ show e
    show (SQid s) = " :qid " ++ s
    show (SNamed s) = " :named " ++ s
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
    _constants :: M.Map String SExp,
    _lengthConstants :: M.Map String SExp,
    _hexConstants :: M.Map String SExp,
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
emitAssertion e = do
    i <- freshSMTName
    emit (SApp [SAtom "assert", SApp [SAtom "!", e, SNamed i]])

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

queryZ3 :: Bool -> String -> IORef (Map String P.Z3Result) -> IORef (M.Map Int Bool) -> String -> IO (Either String (Bool, Maybe String))
queryZ3 logsmt filepath z3results mp q = do
    let hq = hash q 
    m <- readIORef mp
    case M.lookup hq m of
      Just res -> return $ Right (res, Nothing)
      Nothing -> do 
          resp <- readProcessWithExitCode "z3" ["-smt2", "-st", "-in"] q
          case resp of
            (ExitSuccess, s, _) -> do                           
              pres <- P.runParserT P.parseZ3Result () "" s
              case pres of
                Left err -> do
                    putStrLn $ "Z3 parse error on " ++ s
                    putStrLn q
                    return $ Left $ "Z3 ERROR: " ++ show err
                Right z3result -> do
                    fn <- case logsmt of
                            False -> return Nothing
                            True -> do
                              b <- logSMT filepath $ q
                              modifyIORef z3results ((b, z3result) :)
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
            Left err -> typeError $ "Z3 error: " ++ err   
              
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



-- Smart app
sApp :: [SExp] -> SExp
sApp [x] = x
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

lengthConstant :: String -> Sym SExp
lengthConstant s = 
    case s of
      "nonce" -> return $ SApp [SAtom "NameKindLength", SAtom "Nonce"]    
      "DH" -> return $ SApp [SAtom "NameKindLength", SAtom "DHkey"]
      "enckey" -> return $ SApp [SAtom "NameKindLength", SAtom "Enckey"]
      "pkekey" -> return $ SApp [SAtom "NameKindLength", SAtom "PKEkey"]
      "sigkey" -> return $ SApp [SAtom "NameKindLength", SAtom "Sigkey"]
      "prfkey" -> return $ SApp [SAtom "NameKindLength", SAtom "PRFkey"]
      "mackey" -> return $ SApp [SAtom "NameKindLength", SAtom "MACkey"]
      "signature" -> return $ SAtom "SignatureLen"
      "vk" -> return $ SAtom "VKLen"
      "maclen" -> return $ SAtom "MAClen"
      "tag" -> return $ SAtom "Taglen"
      "counter" -> return $ SAtom "Counterlen"
      "crh" -> return $ SAtom "CrhLength"

symLenConst :: String -> Sym SExp
symLenConst s = do
    v <- lengthConstant s
    return $ SApp [SAtom "I2B", v]

sLength :: SExp -> SExp
sLength e = SApp [SAtom "length", e]

bTrue :: SExp
bTrue = SAtom "TRUE"

bFalse :: SExp
bFalse = SAtom "FALSE"

unit :: SExp
unit = SAtom "UNIT"

interpretAExp :: AExpr -> Sym SExp
interpretAExp ae' = do
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
      AEPreimage p ps as -> do
          aes <- liftCheck $ getROPreimage p ps as
          interpretAExp aes
      AEGet ne -> do
          liftCheck $ debug $ owlpretty "AEGet" <+> owlpretty ne
          symNameExp ne
      AEGetEncPK ne -> interpretAExp $ aeApp (topLevelPath  "enc_pk") [] [mkSpanned $ AEGet ne]
      AEGetVK ne -> interpretAExp $ aeApp (topLevelPath  "vk") [] [mkSpanned $ AEGet ne]
      AEPackIdx i a -> interpretAExp a

sName :: Bool -> String -> [SExp] -> Maybe ([AExpr], Int) -> Sym SExp
sName isRO n ivs oi = do
    (vn, argvs) <- case oi of
               Nothing -> return $ (if isRO then (SAtom $ "%name_" ++ n ++ "_0") else (SAtom $ "%name_" ++ n), [])
               Just (as, i) -> do
                   argvs <- mapM interpretAExp as
                   return $ (SAtom $ "%name_" ++ n ++ "_" ++ (show i), argvs)
    return $ sApp $ vn : ivs ++ argvs

withIndices :: [(IdxVar, IdxType)] -> Sym a -> Sym a
withIndices xs k = do
    sIE <- use symIndexEnv
    symIndexEnv %= (M.union $ M.fromList $ map (\(i, _) -> (i, SAtom $ show i)) xs) 
    res <- local (over inScopeIndices $ (++) xs) k
    symIndexEnv .= sIE
    return res

withSMTVars :: [DataVar] -> Sym a -> Sym a
withSMTVars xs k = do
    vVs <- use varVals
    varVals %= (M.union $ M.fromList $ map (\v -> (v, SAtom $ show v)) xs)
    let tyc = map (\v -> (v, (ignore $ show v, Nothing, tData advLbl advLbl))) xs -- The label on the type here is arbitrary
    res <- local (over tyContext $ (++) tyc) k
    varVals .= vVs
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
          liftCheck $ typeError (show $ owlpretty "SMT ERROR: unknown index " <> owlpretty v <> owlpretty " under inScopeIndices " <> owlpretty (map fst indices))

data SMTNameDef = 
    SMTBaseName (SExp, ResolvedPath) (Bind ([IdxVar], [IdxVar]) (Maybe NameType))
      | SMTROName (SExp, ResolvedPath) Int (Bind (([IdxVar], [IdxVar]), [DataVar]) NameType)

withSMTNameDef :: SMTNameDef -> ((SExp, ResolvedPath) -> Maybe Int -> (([IdxVar], [IdxVar]), [DataVar]) -> Maybe NameType -> Sym a) -> Sym a                      
withSMTNameDef df k = do
    case df of
      SMTBaseName p b -> do
          (idxs, ont) <- liftCheck $ unbind b
          k p Nothing (idxs, []) ont
      SMTROName p i b -> do
          (idxs_xs, nt) <- liftCheck $ unbind b
          k p (Just i) idxs_xs (Just nt)

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
          RODef _ b -> do
              sn <- smtName n
              (xs, (a, p, nts)) <- liftCheck $ unbind b
              return $ map (\i -> SMTROName ((SAtom $ "%name_" ++ sn ++ "_" ++ (show i)), n) i (bind ((is, ps), xs) (nts !! i))) [0 .. (length nts - 1)] 
    return $ concat ys
            
getSymName :: NameExp -> Sym SExp
getSymName ne = do 
    liftCheck $ debug $ owlpretty "getSymName" <+> owlpretty ne
    ne' <- liftCheck $ normalizeNameExp ne
    case ne'^.val of
      NameConst (is1, is2) s oi -> do
        sn <- smtName s
        vs1 <- mapM symIndex is1
        vs2 <- mapM symIndex is2
        isRO <- liftCheck $ isNameDefRO s
        sName isRO sn (vs1 ++ vs2) oi
      PRFName ne1 s -> do
          n <- getSymName ne1
          return $ SApp [SAtom "PRFName", n, SAtom $ "\"" ++ s ++ "\""]

symNameExp :: NameExp -> Sym SExp
symNameExp ne = do
    liftCheck $ debug $ owlpretty "symNameExp" <+> owlpretty ne
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

instance OwlPretty CanonLabel where
    owlpretty (CanonAnd cs) = 
        mconcat $ intersperse (owlpretty " /\\ ") (map owlpretty cs) 

instance OwlPretty CanonLabelBig where        
    owlpretty (CanonNoBig ca) = owlpretty ca
    owlpretty (CanonBig ia) = 
        let (is, a) = owlprettyBind ia in 
        owlpretty "/\\_" <> is <> owlpretty "(" <> a <> owlpretty ")"

instance OwlPretty CanonAtom where
    owlpretty (CanonLName a) = owlpretty (nameLbl a)
    owlpretty (CanonAdv) = owlpretty advLbl
    owlpretty (CanonTop) = owlpretty topLbl
    owlpretty (CanonZero) = owlpretty zeroLbl
