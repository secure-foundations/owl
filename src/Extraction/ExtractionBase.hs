{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuasiQuotes #-}
module ExtractionBase where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Data.Char
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Lens
import Prettyprinter
import Pretty
import Data.Type.Equality
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name ( Name(Bn, Fn) )
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Unbound.Generics.LocallyNameless.TH ()
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import AST
import CmdArgs
import System.IO
import qualified TypingBase as TB
import qualified SMTBase as SMT
import ConcreteAST
import Verus
import PrettyVerus
import Prettyprinter.Interpolate

newtype ExtractionMonad t a = ExtractionMonad (ReaderT (TB.Env SMT.SolverEnv) (StateT (Env t) (ExceptT ExtractionError IO)) a)
    deriving (Functor, Applicative, Monad, MonadState (Env t), MonadError ExtractionError, MonadIO, MonadReader (TB.Env SMT.SolverEnv))

runExtractionMonad :: (TB.Env SMT.SolverEnv) -> Env t -> ExtractionMonad t a -> IO (Either ExtractionError a)
runExtractionMonad tcEnv env (ExtractionMonad m) = runExceptT . evalStateT (runReaderT m tcEnv) $ env

liftCheck :: TB.Check' SMT.SolverEnv a -> ExtractionMonad t a
liftCheck c = do
    e <- ask
    o <- liftIO $ runExceptT $ runReaderT (TB.unCheck $ local (set TB.tcScope $ TB.TcGhost False) c) e
    case o of 
      Left s -> ExtractionMonad $ lift $ throwError $ ErrSomethingFailed $ "liftCheck error: "
      Right i -> return i



data Env t = Env {
        _flags :: Flags
    ,   _path :: String
    ,   _freshCtr :: Integer
    ,   _varCtx :: M.Map (CDataVar t) t
    ,   _funcs :: M.Map String ([FormatTy], FormatTy) -- function name -> (arg types, return type)
    ,   _owlUserFuncs :: M.Map String (TB.UserFunc, Maybe (FormatTy, FormatTy)) -- (return type for pub and sec (Just if needs extraction))
    ,   _memoKDF :: [(([NameKind], [AExpr]), (CDataVar t, t))]
    ,   _genVerusNameEnv :: M.Map String VNameData -- For GenVerus, need to store all the local and shared names so we know their types
    ,   _genVerusPkEnv :: M.Map String VNameData -- For GenVerus, need to store all the public keys so we know their types
}



-- TODO: these may not all be needed
data ExtractionError =
      CantLayoutType Ty
    | TypeError String
    | UndefinedSymbol String
    | OutputWithUnknownDestination
    | LocalityWithNoMain String
    | UnsupportedOracleReturnType String
    | UnsupportedNameExp NameExp
    | UnsupportedNameType NameType
    | UnsupportedDecl String
    | DefWithTooManySids String
    | NameWithTooManySids String
    | UnsupportedSharedIndices String
    | CouldntParseInclude String
    | OddLengthHexConst
    | PreimageInExec String
    | GhostInExec String
    | LiftedError ExtractionError
    | CantCastType String String String
    | ErrSomethingFailed String

instance OwlPretty ExtractionError where
    owlpretty (CantLayoutType t) =
        owlpretty "Can't make a layout for type:" <+> owlpretty t
    owlpretty (TypeError s) =
        owlpretty "Type error during extraction:" <+> owlpretty s
    owlpretty (UndefinedSymbol s) =
        owlpretty "Undefined symbol: " <+> owlpretty s
    owlpretty OutputWithUnknownDestination =
        owlpretty "Found a call to `output` without a destination specified. For extraction, all outputs must have a destination locality specified."
    owlpretty (LocalityWithNoMain s) =
        owlpretty "Locality" <+> owlpretty s <+> owlpretty "does not have a defined main function. For extraction, there should be a defined entry point function that must not take arguments: def" <+> owlpretty s <> owlpretty "_main () @" <+> owlpretty s
    owlpretty (UnsupportedOracleReturnType s) =
        owlpretty "Oracle" <+> owlpretty s <+> owlpretty "does not return a supported oracle return type for extraction."
    owlpretty (UnsupportedNameExp ne) =
        owlpretty "Name expression" <+> owlpretty ne <+> owlpretty "is unsupported for extraction."
    owlpretty (UnsupportedNameType nt) =
        owlpretty "Name type" <+> owlpretty nt <+> owlpretty "is unsupported for extraction."
    owlpretty (UnsupportedDecl s) =
        owlpretty "Unsupported decl type for extraction:" <+> owlpretty s
    owlpretty (DefWithTooManySids s) =
        owlpretty "Owl procedure" <+> owlpretty s <+> owlpretty "has too many sessionID parameters. For extraction, each procedure can have at most one sessionID parameter"
    owlpretty (NameWithTooManySids s) =
        owlpretty "Owl name" <+> owlpretty s <+> owlpretty "has too many sessionID parameters. For extraction, each procedure can have at most one sessionID parameter"
    owlpretty (UnsupportedSharedIndices s) =
        owlpretty "Unsupported sharing of indexed name:" <+> owlpretty s
    owlpretty (CouldntParseInclude s) =
        owlpretty "Couldn't parse included file:" <+> owlpretty s
    owlpretty OddLengthHexConst =
        owlpretty "Found a hex constant with an odd length, which should not be allowed."
    owlpretty (PreimageInExec s) =
        owlpretty "Found a call to `preimage`, which is not allowed in exec code:" <+> owlpretty s
    owlpretty (GhostInExec s) =
        owlpretty "Found a ghost value in exec code:" <+> owlpretty s
    owlpretty (LiftedError e) =
        owlpretty "Lifted error:" <+> owlpretty e
    owlpretty (CantCastType v t1 t2) =
        owlpretty "Can't cast value" <+> owlpretty v <+> owlpretty "from type" <+> owlpretty t1 <+> owlpretty "to type" <+> owlpretty t2
    owlpretty (ErrSomethingFailed s) =
        owlpretty "Extraction failed with message:" <+> owlpretty s

type LocalityName = String
type NameData = (String, FLen, Int, BufSecrecy) -- name, type, number of processID indices, whether should be SecretBuf or OwlBuf
type VNameData = (String, ConstUsize, Int, BufSecrecy)
type OwlDefData = (String, TB.Def)
data LocalityData nameData defData = LocalityData {
    _nLocIdxs :: Int, 
    _localNames :: [nameData], 
    _sharedNames :: [nameData], 
    _defs :: [defData], 
    _tables :: [(String, Ty)], 
    _counters :: [String]
} deriving Show
makeLenses ''LocalityData
data ExtractionData defData tyData nameData userFuncData = ExtractionData {
    _locMap :: M.Map LocalityName (LocalityData nameData defData),
    _presharedNames :: [(nameData, [LocalityName])],
    _pubKeys :: [nameData],
    _tyDefs :: [(String, tyData)],
    _userFuncs :: [userFuncData]
} deriving Show
makeLenses ''ExtractionData

type OwlExtractionData = ExtractionData OwlDefData TB.TyDef NameData (String, TB.UserFunc)
type OwlLocalityData = LocalityData NameData OwlDefData
type CFExtractionData = ExtractionData (Maybe (CDef FormatTy)) (CTyDef FormatTy) NameData (CUserFunc FormatTy)
type CRExtractionData = ExtractionData (Maybe (CDef VerusTy)) (CTyDef (Maybe ConstUsize, VerusTy)) VNameData (CUserFunc VerusTy)
type FormatLocalityData = LocalityData NameData (Maybe (CDef FormatTy))
type VerusLocalityData = LocalityData VNameData (Maybe (CDef VerusTy))


makeLenses ''Env

liftExtractionMonad :: ExtractionMonad t a -> ExtractionMonad t' a
liftExtractionMonad m = do
    tcEnv <- ask
    env' <- get
    let env = Env {
            _flags = env' ^. flags,
            _path = env' ^. path,
            _freshCtr = env' ^. freshCtr,
            _varCtx = M.empty,
            _funcs = env' ^. funcs,
            _owlUserFuncs = env' ^. owlUserFuncs,
            _memoKDF = [],
            _genVerusNameEnv = M.empty,
            _genVerusPkEnv = M.empty
        }
    o <- liftIO $ runExtractionMonad tcEnv env m
    case o of 
        Left s -> throwError $ LiftedError s
        Right i -> return i



lookupVar :: CDataVar t -> ExtractionMonad t (Maybe t)
lookupVar x = do
    s <- use varCtx
    return $ M.lookup x s

printErr :: ExtractionError -> IO ()
printErr e = print $ owlpretty "Extraction error:" <+> owlpretty e

debugPrint :: String -> ExtractionMonad t ()
debugPrint = liftIO . putStrLn

debugLog :: String -> ExtractionMonad t ()
debugLog s = do
    fs <- use flags
    when (fs ^. fDebugExtraction) $ debugPrint ("    " ++ s)

instance Fresh (ExtractionMonad t) where
    fresh (Fn s _) = do
        n <- use freshCtr
        freshCtr %= (+) 1
        return $ Fn s n
    fresh nm@(Bn {}) = return nm

initEnv :: Flags -> String -> [(String, TB.UserFunc)] -> Env t
initEnv flags path owlUserFuncs = Env flags path 0 M.empty M.empty (mkUFs owlUserFuncs) [] M.empty M.empty
    where
        mkUFs :: [(String, TB.UserFunc)] -> M.Map String (TB.UserFunc, Maybe (FormatTy, FormatTy))
        mkUFs l = M.fromList $ map (\(s, uf) -> (s, (uf, Nothing))) l


flattenResolvedPath :: ResolvedPath -> String
flattenResolvedPath PTop = ""
flattenResolvedPath (PDot PTop y) = y
flattenResolvedPath (PDot x y) = flattenResolvedPath x ++ "_" ++ y
flattenResolvedPath s = error $ "failed flattenResolvedPath on " ++ show s

tailPath :: Path -> ExtractionMonad t String
tailPath (PRes (PDot _ y)) = return y
tailPath p = throwError $ ErrSomethingFailed $ "couldn't do tailPath of path " ++ show p

flattenPath :: Path -> ExtractionMonad t String
flattenPath (PRes rp) = do
    rp' <- liftCheck $ TB.normResolvedPath rp
    return $ flattenResolvedPath rp'
flattenPath p = error $ "bad path: " ++ show p



unbindCDepBind :: (Alpha a, Alpha t, Typeable t) => CDepBind t a -> ExtractionMonad tt ([(CDataVar t, String, t)], a)
unbindCDepBind (CDPDone a) = return ([], a)
unbindCDepBind (CDPVar t s xd) = do
    (x, d) <- unbind xd 
    (xs, a) <- unbindCDepBind d 
    return ((x, s, t) : xs, a)

bindCDepBind :: (Alpha a, Alpha t, Typeable t) => [(CDataVar t, String, t)] -> a -> ExtractionMonad tt (CDepBind t a)
bindCDepBind [] a = return $ CDPDone a
bindCDepBind ((x, s, t):xs) a = do
    d <- bindCDepBind xs a
    return $ CDPVar t s (bind x d)

replacePrimes :: String -> String
replacePrimes = map (\c -> if c == '\'' || c == '.' then '_' else c)

execName :: String -> VerusName
execName owlName = "owl_" ++ replacePrimes owlName

-- cmpNameLifetime :: String -> String -> VerusName
-- cmpNameLifetime owlName lt = withLifetime ("owl_" ++ owlName) lt

specName :: String -> VerusName
specName owlName = "owlSpec_" ++ replacePrimes owlName

unExecName :: VerusName -> String
unExecName s = 
    if "owl_" `isPrefixOf` s then drop 4 s else error "unExecName: not an owl name: " ++ s

specNameOfExecName :: VerusName -> String
specNameOfExecName s = 
    if "owl_" `isPrefixOf` s then specName $ drop 4 s else error "specNameOf: not an owl name: " ++ s

fLenOfNameKind :: NameKind -> ExtractionMonad t FLen
fLenOfNameKind nk = do
    return $ FLNamed $ case nk of
        NK_KDF -> "kdfkey"
        NK_DH  -> "group"
        NK_Enc -> "enckey"
        NK_PKE -> "pkekey"
        NK_Sig -> "sigkey"
        NK_MAC -> "mackey"
        NK_KEM -> "kemkey"
        NK_Nonce s -> s

fLenOfNameTy :: NameType -> ExtractionMonad t FLen
fLenOfNameTy nt = do
    nk <- nameKindOfNameTy nt
    fLenOfNameKind nk

-- TB.getNameKind has no case for KEM keys (NT_KEM), so it is wrapped here
nameKindOfNameTy :: NameType -> ExtractionMonad t NameKind
nameKindOfNameTy nt =
    case nt ^. val of
        NT_KEM _ -> return NK_KEM
        NT_App p ps as -> liftCheck (TB.resolveNameTypeApp p ps as) >>= nameKindOfNameTy
        _ -> liftCheck $ TB.getNameKind nt

-- KEM (ML-KEM / Kyber) shared secrets are always this many bytes long
kemSharedSecretLen :: Int
kemSharedSecretLen = 32

-- The length of the shared secrets KEMName<k, i> of a KEM key k : kemkey(nt), which is
-- the length of nt. Extraction requires it to be the length of a KEM shared secret.
kemSharedSecretFLen :: NameType -> ExtractionMonad t FLen
kemSharedSecretFLen nt = do
    fl <- fLenOfNameTy nt
    l <- concreteLength $ lowerFLen fl
    when (l /= kemSharedSecretLen) $ throwError $ ErrSomethingFailed $
        "the name type of the shared secrets of a KEM key must be " ++ show kemSharedSecretLen
        ++ " bytes long (the KEM's shared secret length), but it is " ++ show l ++ " bytes long"
    return fl


secrecyOfNameKind :: NameKind -> ExtractionMonad t BufSecrecy
secrecyOfNameKind nk = do
    return $ case nk of
        NK_KDF -> BufSecret
        NK_DH  -> BufSecret
        NK_Enc -> BufSecret
        NK_PKE -> BufSecret
        NK_Sig -> BufSecret
        NK_MAC -> BufSecret
        NK_KEM -> BufSecret
        NK_Nonce _ -> BufSecret

secrecyOfNameTy :: NameType -> ExtractionMonad t BufSecrecy
secrecyOfNameTy nt = do
    nk <- nameKindOfNameTy nt
    secrecyOfNameKind nk

concreteLength :: ConstUsize -> ExtractionMonad t Int
concreteLength (CUsizeLit i) = return i
concreteLength (CUsizeConst s) = do
    -- NOTE: these lengths are dependent on the particular crypto primitives being used
    l <- case s of
        "KDFKEY_SIZE"    -> return 32
        "GROUP_SIZE"     -> return 32
        "ENCKEY_SIZE"    -> return 32
        "MACKEY_SIZE"    -> return 64
        "NONCE_SIZE"     -> return 12
        "TAG_SIZE"       -> return 16
        "MACLEN_SIZE"    -> return 16
        "COUNTER_SIZE"   -> return 8
        "SIGNATURE_SIZE" -> return 64
        -- KEM: Kyber1024 / ML-KEM-1024. Secret keys and ciphertexts are in libsignal's
        -- serialized forms, which start with a one-byte key type (0x08 = Kyber1024,
        -- 0x0A = ML-KEM-1024); a public key is a raw Kyber1024 key (see owl_kem.rs)
        "KEMKEY_SIZE"        -> return 3169 -- 1 + 3168 (decapsulation key)
        "KEM_PK_SIZE"        -> return 1568 -- raw encapsulation key
        "KEM_CIPHERLEN_SIZE" -> return 1569 -- 1 + 1568 (ciphertext)
        "KEM_COINS_SIZE"     -> return 32   -- randomness of one encapsulation
        -- The below are for compatibility with old Owl
        "VK_SIZE"        -> return 1219
        "SIGKEY_SIZE"    -> return 1219
        "PKEKEY_SIZE"    -> return 1219
        "PKE_PK_SIZE"    -> return 1219
        _ -> throwError $ UndefinedSymbol $ "concreteLength: unhandled length constant: " ++ s
    debugPrint $ "WARNING: using hardcoded concrete length: " ++ s ++ " = " ++ show l
    return l
concreteLength (CUsizePlus a b) = do
    a' <- concreteLength a
    b' <- concreteLength b
    return $ a' + b'

-- prelude.smt2 bounds the lengths of the kdfInjKinds below by the uninterpreted
-- security parameter MinKDFSliceLen. The concrete key sizes are therefore an
-- upper bound on the values it can take for the extracted code.
reportMaxKDFSliceLen :: ExtractionMonad t ()
reportMaxKDFSliceLen = do
    ls <- forM kdfInjKinds $ \nk -> fLenOfNameKind nk >>= concreteLength . lowerFLen
    debugPrint $ "Security parameter: with these concrete key sizes, MinKDFSliceLen (prelude.smt2) is at most " 
        ++ show (minimum ls) ++ " bytes (the minimum over kdfkey, enckey, mackey)"

lowerLenConst :: String -> String
lowerLenConst s = map toUpper s ++ "_SIZE"

lowerFLen :: FLen -> ConstUsize
lowerFLen (FLConst n) = CUsizeLit n
lowerFLen (FLNamed n) = 
    let n' = lowerLenConst n in
    CUsizeConst n'
lowerFLen (FLPlus a b) = 
    let a' = lowerFLen a in
    let b' = lowerFLen b in
    CUsizePlus a' b'
lowerFLen (FLCipherlen a) = 
    let n' = lowerFLen a in
    CUsizePlus n' (CUsizeConst "TAG_SIZE")


hexStringToByteList :: String -> ExtractionMonad t (Doc ann)
hexStringToByteList [] = return $ pretty ""
hexStringToByteList (h1 : h2 : t) = do
    t' <- hexStringToByteList t
    commaIfNeeded <- if null t then return "" else return ","
    return $ pretty "0x" <> pretty h1 <> pretty h2 <> pretty "u8" <> pretty commaIfNeeded <+> t'
hexStringToByteList _ = throwError OddLengthHexConst

lookupNameKindAExprMap :: [(([NameKind], [AExpr]), a)] -> [NameKind] -> [AExpr] -> Maybe a
lookupNameKindAExprMap [] nks args = Nothing
lookupNameKindAExprMap (((lnks, largs), r) : tl) nks args =
    if all (uncurry (==)) (zip nks lnks) && all (uncurry aeq) (zip args largs)
    then Just r
    else lookupNameKindAExprMap tl nks args


lookupKdfCall :: [NameKind] -> [AExpr] -> ExtractionMonad t (Maybe (CDataVar t, t))
lookupKdfCall nks k = do
    hcs <- use memoKDF
    return $ lookupNameKindAExprMap hcs nks k


---- Equality on FormatTys ignoring buffer secrecy
eqUpToSecrecy :: FormatTy -> FormatTy -> Bool
eqUpToSecrecy (FBuf _ l1) (FBuf _ l2) = l1 == l2 || l1 == Nothing || l2 == Nothing
eqUpToSecrecy (FOption t1) (FOption t2) = eqUpToSecrecy t1 t2
eqUpToSecrecy f1 f2 = f1 == f2

---- Equality on FormatTys ignoring FBuf length
eqUpToBufLen :: FormatTy -> FormatTy -> Bool
eqUpToBufLen (FBuf s1 _) (FBuf s2 _) = s1 == s2
eqUpToBufLen (FOption t1) (FOption t2) = eqUpToBufLen t1 t2
eqUpToBufLen f1 f2 = f1 == f2

secrecyOfFTy :: FormatTy -> BufSecrecy
secrecyOfFTy (FBuf s _) = s
secrecyOfFTy (FStruct _ fs) = if all ((== BufPublic) . secrecyOfFTy . snd) fs then BufPublic else BufSecret
secrecyOfFTy (FEnum _ cs) = if all ((== BufPublic) . secrecyOfFTy) (mapMaybe snd cs) then BufPublic else BufSecret
secrecyOfFTy (FOption f) = secrecyOfFTy f
secrecyOfFTy _ = BufPublic

joinSecrecy :: BufSecrecy -> BufSecrecy -> BufSecrecy
joinSecrecy BufPublic BufPublic = BufPublic
joinSecrecy _ _ = BufSecret

joinSecrecies :: [BufSecrecy] -> BufSecrecy
joinSecrecies = foldr joinSecrecy BufPublic

secretizeFTy :: FormatTy -> FormatTy
secretizeFTy (FBuf _ l) = FBuf BufSecret l
secretizeFTy (FStruct n fs) = FStruct ("secret_" ++ n) $ map (fmap secretizeFTy) fs
secretizeFTy (FEnum n cs) = FEnum n $ map (fmap (fmap secretizeFTy)) cs
secretizeFTy (FOption f) = FOption $ secretizeFTy f
secretizeFTy (FHexConst s) = FBuf BufSecret $ Just $ FLConst $ length s `div` 2
secretizeFTy f = f

------------------------------------------------------------------------------------------------------
---- Vest stuff

-- Any format that uses Vest's `uint` or `Tag` combinators cannot have a secret parser
-- Enums use `Tag` for the enum tag
-- Structs must have all secret-parsable fields to be secret-parsable 
hasSecParser :: FormatTy -> Bool
hasSecParser (FBuf BufSecret _) = True
hasSecParser (FStruct _ fs) = all (hasSecParser . snd) fs
hasSecParser FGhost = True
hasSecParser _ = False 

canSecretParse :: FormatTy -> Bool
canSecretParse f =
    hasSecParser f ||
        case f of
            FStruct _ fs -> any ((==) BufSecret . secrecyOfFTy . snd) fs
            _ -> False

-- For serialization, we don't care if the buf is secret or public to begin with, since we 
-- may need to upcast the public buf to secret when serializing
hasSecSerializer :: FormatTy -> Bool
hasSecSerializer (FBuf _ _) = True
hasSecSerializer (FStruct _ fs) = all (hasSecSerializer . snd) fs
hasSecSerializer FGhost = True
hasSecSerializer _ = False 


mkNestPattern :: [Doc ann] -> Doc ann
mkNestPattern l = 
        case l of
            [] -> pretty ""
            [x] -> x
            x:y:tl -> foldl (\acc v -> parens (acc <+> pretty "," <+> v)) (parens (x <> pretty "," <+> y)) tl 

-- Vest 2.0 sequences formats with the `Pair` combinator. Its values are left-nested tuples,
-- so the value pattern for a nest is still `mkNestPattern`.
mkNestComb :: [Doc ann] -> Doc ann
mkNestComb l =
        case l of
            [] -> pretty ""
            [x] -> x
            x:y:tl -> foldl (\acc v -> [di|Pair(#{acc}, #{v})|]) [di|Pair(#{x}, #{y})|] tl

mkNestCombTy :: [Doc ann] -> Doc ann
mkNestCombTy l =
        case l of
            [] -> pretty ""
            [x] -> x
            x:y:tl -> foldl (\acc v -> [di|Pair<#{acc}, #{v}>|]) [di|Pair<#{x}, #{y}>|] tl

-- Enums are an ordered choice (Vest 2.0 `Choice`, nested to the right) between the
-- cases, each prefixed by a one-byte tag. Parsed values are nested `Sum`s.
nestChoiceTy :: [Doc ann] -> Doc ann
nestChoiceTy l =
    case l of
        [] -> pretty ""
        [x] -> x
        x:tl -> [di|Choice<#{x}, #{nestChoiceTy tl}>|]

nestChoice :: [Doc ann] -> Doc ann
nestChoice l =
    case l of
        [] -> pretty ""
        [x] -> x
        x:tl -> [di|Choice(#{x}, #{nestChoice tl})|]

-- injSum i l x is the value (or pattern) for x in case i of a nested choice of l cases
injSum :: Int -> Int -> Doc ann -> Doc ann
injSum i l x
    | l <= 1 = x
    | i == 0 = [di|Sum::Inl(#{x})|]
    | otherwise = [di|Sum::Inr(#{injSum (i - 1) (l - 1) x})|]

listIdxToInjPat :: Int -> Int -> Doc ann -> ExtractionMonad t (Doc ann)
listIdxToInjPat i l x = return $ injSum i l x

listIdxToInjResult :: Int -> Int -> Doc ann -> ExtractionMonad t (Doc ann)
listIdxToInjResult i l x = return $ injSum i l x


withJustNothing :: (a -> ExtractionMonad t (Maybe b)) -> Maybe a -> ExtractionMonad t (Maybe (Maybe b))
withJustNothing f (Just x) = Just <$> f x
withJustNothing f Nothing = return (Just Nothing)

compareByFieldNames :: (String, a) -> (String, a) -> Ordering
compareByFieldNames (a, _) (b, _) = compare a b

specCombTyOf' :: FormatTy -> ExtractionMonad t (Maybe (Doc ann))
specCombTyOf' (FBuf BufSecret (Just flen)) = do
    return $ Just [di|Varied<usize>|]
specCombTyOf' (FBuf BufSecret Nothing) = do
    return $ Just [di|Tail|]
specCombTyOf' (FBuf BufPublic (Just flen)) = return $ Just [di|Varied<usize>|]
specCombTyOf' (FBuf BufPublic Nothing) = return $ Just [di|Tail|]
specCombTyOf' (FStruct _ fs) = do
    fs' <- mapM (specCombTyOf' . snd) fs
    case sequence fs' of
        Just fs'' -> do
            let nest = mkNestCombTy fs''
            return $ Just [di|#{nest}|]
        Nothing -> return Nothing
specCombTyOf' (FEnum _ csStart) = do
    let cs = sortBy compareByFieldNames csStart
    cs' <- mapM (withJustNothing specCombTyOf' . snd) cs
    case sequence cs' of
        Just cs'' -> do
            let cs''' = map (fromMaybe [di|Varied<usize>|]) cs''
            let nest = nestChoiceTy [ [di|PrefixTagged<U8, u8, #{c}>|] | c <- cs''' ]
            return $ Just [di|#{nest}|]
        Nothing -> return Nothing
specCombTyOf' (FHexConst s) = do
    let l = length s `div` 2
    return $ Just [di|OwlConstBytes<#{l}>|]
specCombTyOf' _ = return Nothing

specCombTyOf :: FormatTy -> ExtractionMonad t (Doc ann)
specCombTyOf = liftFromJust specCombTyOf'

execCombTyOf' :: FormatTy -> ExtractionMonad t (Maybe (Doc ann))
execCombTyOf' (FBuf BufSecret (Just flen)) = return $ Just [di|Varied<usize>|]
execCombTyOf' (FBuf BufSecret Nothing) = return $ Just [di|Tail|]
execCombTyOf' (FBuf BufPublic (Just flen)) = return $ Just [di|Varied<usize>|]
execCombTyOf' (FBuf BufPublic Nothing) = return $ Just [di|Tail|]
execCombTyOf' (FStruct _ fs) = do
    fs' <- mapM (execCombTyOf' . snd) fs
    case sequence fs' of
        Just fs'' -> do
            let nest = mkNestCombTy fs''
            return $ Just [di|#{nest}|]
        Nothing -> return Nothing
execCombTyOf' (FEnum _ csStart) = do
    let cs = sortBy compareByFieldNames csStart
    cs' <- mapM (withJustNothing execCombTyOf' . snd) cs
    case sequence cs' of
        Just cs'' -> do
            let cs''' = map (fromMaybe [di|Varied<usize>|]) cs''
            let nest = nestChoiceTy [ [di|PrefixTagged<U8, u8, #{c}>|] | c <- cs''' ]
            return $ Just [di|#{nest}|]
        Nothing -> return Nothing
execCombTyOf' (FHexConst s) = do
    let l = length s `div` 2
    return $ Just [di|OwlConstBytes<#{l}>|]
execCombTyOf' _ = return Nothing

execCombTyOf :: FormatTy -> ExtractionMonad t (Doc ann)
execCombTyOf = liftFromJust execCombTyOf'

-- (combinator type, any constants that need to be defined)
specCombOf' :: String -> FormatTy -> ExtractionMonad t (Maybe (Doc ann, Doc ann))
specCombOf' _ (FBuf BufSecret (Just flen)) = do
    l <- concreteLength $ lowerFLen flen
    return $ noconst [di|Varied(#{l}usize)|]
specCombOf' _ (FBuf BufSecret Nothing) = return $ noconst [di|Tail|]
specCombOf' _ (FBuf BufPublic (Just flen)) = do
    l <- concreteLength $ lowerFLen flen
    return $ noconst [di|Varied(#{l}usize)|]
specCombOf' _ (FBuf BufPublic Nothing) = return $ noconst [di|Tail|]
specCombOf' constSuffix (FStruct _ fs) = do
    fcs <- mapM (specCombOf' constSuffix . snd) fs
    case sequence fcs of
        Just fcs' -> do
            let (fs', consts) = unzip fcs'
            let nest = mkNestComb fs'
            -- We don't return the consts here, since they would already have been
            -- returned and printed when the nested struct was defined
            return $ noconst [di|#{nest}|]
        Nothing -> return Nothing
specCombOf' constSuffix (FEnum _ csStart) = do
    let cs = sortBy compareByFieldNames csStart
    cs' <- mapM (withJustNothing (specCombOf' constSuffix) . snd) cs
    case sequence cs' of
        Just ccs'' -> do
            let cs'' = foldr (\opt cs -> 
                        case opt of
                            Just (c, const) -> Just c : cs
                            Nothing -> Nothing : cs
                    ) [] ccs''
            let cs''' = map (fromMaybe [di|Varied(0usize)|]) cs''
            let constCs = zipWith (\i c -> [di|PrefixTagged(U8, #{i}u8, #{c})|]) [1 :: Int ..] cs'''
            let nest = nestChoice constCs
            return $ noconst [di|#{nest}|]
        Nothing -> return Nothing
specCombOf' constSuffix (FHexConst s) = do
    let l = length s `div` 2
    bl <- hexStringToByteList s
    let constSuffix' = map Data.Char.toUpper constSuffix
    let const = [di|spec const SPEC_BYTES_CONST_#{s}_#{constSuffix'}: [u8; #{l}] = [#{bl}];|]
    return $ Just ([di|OwlConstBytes::<#{l}>(SPEC_BYTES_CONST_#{s}_#{constSuffix'})|], const)
specCombOf' _ _ = return Nothing

specCombOf :: String -> FormatTy -> ExtractionMonad t (Doc ann, Doc ann)
specCombOf s = liftFromJust (specCombOf' s)

-- (combinator type, any constants that need to be defined)
execCombOf' :: String -> FormatTy -> ExtractionMonad t (Maybe (Doc ann, Doc ann))
execCombOf' _ (FBuf BufSecret (Just flen)) = do
    l <- concreteLength $ lowerFLen flen
    return $ noconst [di|Varied(#{l}usize)|]
execCombOf' _ (FBuf BufSecret Nothing) = return $ noconst [di|Tail|]
execCombOf' _ (FBuf BufPublic (Just flen)) = do
    l <- concreteLength $ lowerFLen flen
    return $ noconst [di|Varied(#{l}usize)|]
execCombOf' _ (FBuf BufPublic Nothing) = return $ noconst [di|Tail|]
execCombOf' constSuffix (FStruct _ fs) = do
    fcs <- mapM (execCombOf' constSuffix . snd) fs
    case sequence fcs of
        Just fcs' -> do
            let (fs', consts) = unzip fcs'
            let nest = mkNestComb fs'
            -- We don't return the consts here, since they would already have been
            -- returned and printed when the nested struct was defined
            return $ noconst [di|#{nest}|]
        Nothing -> return Nothing
execCombOf' constSuffix (FEnum _ csStart) = do
    let cs = sortBy compareByFieldNames csStart
    cs' <- mapM (withJustNothing (specCombOf' constSuffix) . snd) cs
    case sequence cs' of
        Just ccs'' -> do
            let cs'' = foldr (\opt cs -> 
                        case opt of
                            Just (c, const) -> Just c : cs
                            Nothing -> Nothing : cs
                    ) [] ccs''
            let cs''' = map (fromMaybe [di|Varied(0usize)|]) cs''
            let constCs = zipWith (\i c -> [di|PrefixTagged(U8, #{i}u8, #{c})|]) [1 :: Int ..] cs'''
            let nest = nestChoice constCs
            return $ noconst [di|#{nest}|]
        Nothing -> return Nothing
execCombOf' constSuffix (FHexConst s) = do
    bl <- hexStringToByteList s
    let l = length s `div` 2
    let constSuffix' = map Data.Char.toUpper constSuffix
    let const = [__di|
    exec const EXEC_BYTES_CONST_#{s}_#{constSuffix'}: [u8; #{l}] 
        ensures EXEC_BYTES_CONST_#{s}_#{constSuffix'} == SPEC_BYTES_CONST_#{s}_#{constSuffix'} 
    {
        let arr: [u8; #{l}] = [#{bl}];
        assert(arr == SPEC_BYTES_CONST_#{s}_#{constSuffix'});
        arr
    }
    |]
    return $ Just ([di|OwlConstBytes::<#{l}>(EXEC_BYTES_CONST_#{s}_#{constSuffix'})|], const)
execCombOf' _ _ = return Nothing

execCombOf :: String -> FormatTy -> ExtractionMonad t (Doc ann, Doc ann)
execCombOf s = liftFromJust (execCombOf' s)


execParsleyCombOf' :: String -> FormatTy -> ExtractionMonad t (Maybe ParsleyCombinator)
execParsleyCombOf' _ (FBuf BufPublic (Just flen)) = do
    return $ Just $ PCBytes flen
execParsleyCombOf' _ (FBuf BufPublic Nothing) = return $ Just $ PCTail
execParsleyCombOf' constSuffix (FHexConst s) = do
    let constSuffix' = map Data.Char.toUpper constSuffix
    let len = length s `div` 2
    return $ Just $ PCConstBytes len $ "EXEC_BYTES_CONST_" ++ s ++ "_" ++ constSuffix'
execParsleyCombOf' _ _ = return Nothing

execParsleyCombOf :: String -> FormatTy -> ExtractionMonad t ParsleyCombinator
execParsleyCombOf s = liftFromJust (execParsleyCombOf' s)

noconst :: a -> Maybe (a, Doc ann)
noconst x = Just (x, [di||])

liftFromJust :: (a -> ExtractionMonad t (Maybe b)) -> a -> ExtractionMonad t b
liftFromJust f x = do
    res <- f x
    case res of
        Just r -> return r
        Nothing -> throwError $ ErrSomethingFailed "liftFromJust failed"
