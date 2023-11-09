{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module ExtractionBase where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List
import Data.Maybe
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
import Unbound.Generics.LocallyNameless.TH
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import AST
import CmdArgs
import ConcreteAST
import System.IO
import qualified TypingBase as TB

newtype ExtractionMonad a = ExtractionMonad (ReaderT TB.Env (StateT Env (ExceptT ExtractionError IO)) a)
    deriving (Functor, Applicative, Monad, MonadState Env, MonadError ExtractionError, MonadIO, MonadReader TB.Env)

runExtractionMonad :: TB.Env -> Env -> ExtractionMonad a -> IO (Either ExtractionError a)
runExtractionMonad tcEnv env (ExtractionMonad m) = runExceptT . evalStateT (runReaderT m tcEnv) $ env

liftCheck :: TB.Check a -> ExtractionMonad a
liftCheck c = do
    e <- ask
    o <- liftIO $ runExceptT $ runReaderT (TB.unCheck $ local (set TB.tcScope TB.TcGhost) c) e
    case o of 
      Left s -> ExtractionMonad $ lift $ throwError $ ErrSomethingFailed $ "flattenPath error: " 
      Right i -> return i

data RustTy = VecU8 | Bool | Number | String | Unit | ADT String | Option RustTy | Rc RustTy
    deriving (Show, Eq, Generic, Typeable)

instance OwlPretty RustTy where
  owlpretty VecU8 = owlpretty "Vec<u8>"
  owlpretty Bool = owlpretty "bool"
  owlpretty Number = owlpretty "usize" --should just work
  owlpretty String = owlpretty "String"
  owlpretty Unit = owlpretty "()"
  owlpretty (ADT s) = owlpretty s
  owlpretty (Option r) = owlpretty "Option" <> angles (owlpretty r)
  owlpretty (Rc r) = owlpretty "Rc" <> angles (owlpretty r)
 
data SpecTy = SpecSeqU8 | SpecBool | SpecNumber | SpecString | SpecUnit | SpecADT String | SpecOption SpecTy
    deriving (Show, Eq, Generic, Typeable)

instance OwlPretty SpecTy where
  owlpretty SpecSeqU8 = owlpretty "Seq<u8>"
  owlpretty SpecBool = owlpretty "bool"
  owlpretty SpecNumber = owlpretty "usize"
  owlpretty SpecString = owlpretty "String"
  owlpretty SpecUnit = owlpretty "()"
  owlpretty (SpecADT s) = owlpretty s
  owlpretty (SpecOption r) = owlpretty "Option" <> angles (owlpretty r)

type OwlFunDef = Bind (([IdxVar], [IdxVar]), [DataVar]) AExpr

data Env = Env {
    _flags :: Flags,
    _path :: String,
    _aeadCipherMode :: AEADCipherMode,
    _hmacMode :: HMACMode,
    _owlUserFuncs :: [(String, TB.UserFunc)],
    _funcs :: M.Map String ([(RustTy, String)] -> ExtractionMonad (RustTy, String)), -- return type, how to print
    _adtFuncs :: M.Map String (String, RustTy, Bool, [(RustTy, String)] -> ExtractionMonad  String),
    _specAdtFuncs :: S.Set String,
    _typeLayouts :: M.Map String Layout,
    _lenConsts :: M.Map String Int,
    _structs :: M.Map String [(String, RustTy)], -- rust type for each field
    _enums :: M.Map (S.Set String) (String, M.Map String (Maybe RustTy)),
    _oracles :: M.Map String ([String], M.Map Int ([String], [String], Layout)), -- how to print the output length, where to slice to get the subparts
    _includes :: S.Set String, -- files we have included so far
    _freshCtr :: Integer,
    _curRetTy :: Maybe String, -- return type of the def currently being extracted (needed for type annotations)
    _hashCalls :: [((String, [AExpr]), (RustTy, String))], -- key is (roname, aexpr args), can't use M.Map with AExpr keys
    _adtCalls :: [((String, [AExpr]), (RustTy, String))], -- key is (adt name, aexpr args)
    _userFuncsCompiled :: M.Map String (OwlDoc, OwlDoc) -- (compiled spec, compiled exec)
}

data AEADCipherMode = Aes128Gcm | Aes256Gcm | Chacha20Poly1305 deriving (Show, Eq, Generic, Typeable)

data HMACMode = Sha1 | Sha256 | Sha384 | Sha512 deriving (Show, Eq, Generic, Typeable)

defaultCipher :: AEADCipherMode
defaultCipher = Chacha20Poly1305

defaultHMACMode :: HMACMode
defaultHMACMode = Sha512
data Layout =
  LBytes Int -- number of bytes
  | LUnboundedBytes -- Bytes without statically knowable length. Restricted to be the last field in a struct.
  | LStruct String [(String, Layout)] -- field, layout
  | LEnum String (M.Map String (Int, Maybe Layout)) -- finite map from tags to (tag byte, layout)
    deriving (Show, Eq, Generic, Typeable)

instance OwlPretty Layout where
    owlpretty (LBytes i) = owlpretty "bytes" <> parens (owlpretty i)
    owlpretty LUnboundedBytes = owlpretty "unbounded_bytes"
    owlpretty (LStruct name fields) = owlpretty "struct" <+> owlpretty name <> owlpretty ":" <+> owlpretty fields
    owlpretty (LEnum name cases) = owlpretty "enum" <+> owlpretty name <> owlpretty ":" <+> owlpretty (M.keys cases)

data ExtractionError =
      CantLayoutType CTy
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
    | ErrSomethingFailed String

instance OwlPretty ExtractionError where
    owlpretty (CantLayoutType ct) =
        owlpretty "Can't make a layout for type:" <+> owlpretty ct
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
    owlpretty (ErrSomethingFailed s) =
        owlpretty "Extraction failed with message:" <+> owlpretty s

printErr :: ExtractionError -> IO ()
printErr e = print $ owlpretty "Extraction error:" <+> owlpretty e

debugPrint :: String -> ExtractionMonad ()
debugPrint = liftIO . putStrLn

replacePrimes :: String -> String
replacePrimes = map (\c -> if c == '\'' || c == '.' then '_' else c)

replacePrimes' :: OwlDoc -> OwlDoc
replacePrimes' = owlpretty . replacePrimes . show

rustifyName :: String -> String
rustifyName s = "owl_" ++ replacePrimes s

rustifyName' :: OwlDoc -> OwlDoc
rustifyName' = owlpretty . rustifyName . show

unrustifyName :: String -> String
unrustifyName = drop 4

specName :: String -> String
specName s = "owlSpec_" ++ replacePrimes s

flattenResolvedPath :: ResolvedPath -> String
flattenResolvedPath PTop = ""
flattenResolvedPath (PDot PTop y) = y
flattenResolvedPath (PDot x y) = flattenResolvedPath x ++ "_" ++ y
flattenResolvedPath s = error $ "failed flattenResolvedPath on " ++ show s


tailPath :: Path -> ExtractionMonad String
tailPath (PRes (PDot _ y)) = return y
tailPath p = throwError $ ErrSomethingFailed $ "couldn't do tailPath of path " ++ show p

flattenPath :: Path -> ExtractionMonad String
flattenPath (PRes rp) = do
    rp' <- liftCheck $ TB.normResolvedPath rp
    return $ flattenResolvedPath rp'
flattenPath p = error $ "bad path: " ++ show p

locName :: String -> String
locName x = "loc_" ++ replacePrimes x

cfgName :: String -> String
cfgName x = "cfg_" ++ replacePrimes x

stateName :: String -> String
stateName x = "state_" ++ replacePrimes x

sidName :: String -> String
sidName x = "sid_" ++ replacePrimes x

makeLenses ''Env

debugLog :: String -> ExtractionMonad ()
debugLog s = do
    fs <- use flags
    when (fs ^. fDebugExtraction) $ debugPrint ("    " ++ s)

instance Fresh ExtractionMonad where
    fresh (Fn s _) = do
        n <- use freshCtr
        freshCtr %= (+) 1
        return $ Fn s n
    fresh nm@(Bn {}) = return nm

showAEADCipher :: ExtractionMonad String
showAEADCipher = do
    c <- use aeadCipherMode
    return $ case c of
        Aes128Gcm -> "owl_aead::Mode::Aes128Gcm"
        Aes256Gcm -> "owl_aead::Mode::Aes256Gcm"
        Chacha20Poly1305 -> "owl_aead::Mode::Chacha20Poly1305"

showHMACMode :: ExtractionMonad String
showHMACMode = do
    h <- use hmacMode
    return $ case h of
        Sha1 -> "owl_hmac::Mode::Sha1"
        Sha256 -> "owl_hmac::Mode::Sha256"
        Sha384 -> "owl_hmac::Mode::Sha384"
        Sha512 -> "owl_hmac::Mode::Sha512"

aeadKeySize :: AEADCipherMode -> Int
aeadKeySize c = case c of
       Aes128Gcm -> 16
       Aes256Gcm -> 32
       Chacha20Poly1305 -> 32

useAeadKeySize :: ExtractionMonad Int
useAeadKeySize = do
    c <- use aeadCipherMode
    return $ aeadKeySize c

aeadTagSize :: AEADCipherMode -> Int
aeadTagSize c = case c of
       Aes128Gcm -> 16
       Aes256Gcm -> 16
       Chacha20Poly1305 -> 16

useAeadTagSize :: ExtractionMonad Int
useAeadTagSize = do
    c <- use aeadCipherMode
    return $ aeadTagSize c

aeadNonceSize :: AEADCipherMode -> Int
aeadNonceSize c = case c of
       Aes128Gcm -> 12
       Aes256Gcm -> 12
       Chacha20Poly1305 -> 12

useAeadNonceSize :: ExtractionMonad Int
useAeadNonceSize = do
    c <- use aeadCipherMode
    return $ aeadNonceSize c

hmacKeySize :: Int
hmacKeySize = 64

useHmacKeySize :: ExtractionMonad Int
useHmacKeySize = return hmacKeySize

pkeKeySize :: Int
pkeKeySize = 1219

pkePubKeySize :: Int
pkePubKeySize = 1219

sigKeySize :: Int
sigKeySize = 1219

vkSize :: Int
vkSize = 1219

dhSize :: Int
dhSize = 91

hmacLen :: Int
hmacLen = 64

counterSize :: Int
counterSize = 8 -- TODO This is specific to Wireguard---should be a param

crhSize :: Int
crhSize = 32 -- TODO This is specific to Wireguard

initLenConsts :: M.Map String Int
initLenConsts = M.fromList [
        (rustifyName "signature", 256),
        (rustifyName "enckey", aeadKeySize defaultCipher),
        (rustifyName "nonce", aeadNonceSize defaultCipher),
        (rustifyName "mackey", hmacKeySize),
        (rustifyName "maclen", hmacLen),
        (rustifyName "pke_sk", pkeKeySize),
        (rustifyName "pke_pk", pkePubKeySize),
        (rustifyName "sigkey", sigKeySize),
        (rustifyName "vk", vkSize),
        (rustifyName "DH", dhSize),
        (rustifyName "group", dhSize),
        (rustifyName "counter", counterSize),
        (rustifyName "crh", crhSize),
        (rustifyName "tag", 1)
    ]

initTypeLayouts :: M.Map String Layout
initTypeLayouts = M.map LBytes initLenConsts

-- Confirm: we call `serialize` when we need to treat an ADT as a sequence of bytes for a crypto op
printOwlArg :: (RustTy, String) -> String
printOwlArg (Rc VecU8, s) = "&(*" ++ s ++ ").as_slice()"
printOwlArg (VecU8, s) = "&" ++ s ++ ".as_slice()"
printOwlArg (ADT name, s) = "&(serialize_" ++ name ++ "(&" ++ s ++ ")).as_slice()"
printOwlArg (Rc (ADT name), s) = "&(serialize_" ++ name ++ "(&(*" ++ s ++ "))).as_slice()"
printOwlArg (_, s) = s

printOwlOp :: String -> [(RustTy, String)] -> String
printOwlOp op args = op ++ "(" ++ (foldl1 (\acc s -> acc ++ ", " ++ s) . map printOwlArg $ args) ++ ")"


initFuncs :: M.Map String ([(RustTy, String)] -> ExtractionMonad (RustTy, String))
initFuncs = 
    let eqChecker = (\args -> case args of
                                [(Bool, x), (Bool, y)] -> return $ (Bool, x ++ " == " ++ y)
                                [(Number, x), (Number, y)] -> return $ (Bool, x ++ " == " ++ y)
                                [(String, x), (String, y)] -> return $ (Bool, x ++ " == " ++ y)
                                [(Unit, x), (Unit, y)] -> return $ (Bool, x ++ " == " ++ y)
                                [(ADT _,x), (ADT _,y)] -> return $ (Bool, "rc_vec_eq(&" ++ x ++ ".data, &" ++ y ++ ".data)")
                                [(Rc VecU8, x), (Rc VecU8, y)] -> return $ (Bool, "rc_vec_eq(&" ++ x ++ ", &" ++ y ++ ")")
                                [(VecU8, x), (VecU8, y)] -> return $ (Bool, "vec_eq(&" ++ x ++ ".data, &" ++ y ++ ".data)")
                                _ -> throwError $ TypeError $ "got wrong args for eq"
                        ) 
    in M.fromList [
            ("eq", eqChecker),
            ("checknonce", eqChecker),
            ("dhpk", (\args -> case args of
                    [x] -> do return $ (Rc VecU8, printOwlOp "owl_dhpk" [x])
                    _ -> throwError $ TypeError $ "got wrong number of args for dhpk"
            )),
            ("dh_combine", (\args -> case args of
                    [pk, sk] -> do return $ (Rc VecU8, printOwlOp "owl_dh_combine" [pk, sk]) 
                    _ -> throwError $ TypeError $ "got wrong number of args for dh_combine"
            )),
            ("unit", (\_ -> return (Unit, "()"))),
            ("true", (\_ -> return (Bool, "true"))),
            ("false", (\_ -> return (Bool, "false"))),
            ("Some", (\args -> case args of
                    [(t,x)] -> return $ (Option t, "Some(" ++ x ++ ")")
                    _ -> throwError $ TypeError $ "got wrong number of args for Some"
            )),
            ("None", (\_ -> return (Option Unit, "None"))), -- dummy
            ("length", (\args -> case args of
                    [(Rc VecU8,x)] -> return $ (Number, "(*" ++ x ++ ").len()")
                    [(_,x)] -> return $ (Number, x ++ ".len()")
                    _ -> throwError $ TypeError $ "got wrong number of args for length"
            )),
            ("zero", (\_ -> return (Number, "0"))),
            ("plus", (\args -> case args of
                    [(Number, x), (Number, y)] -> return $ (Number, x ++ " + " ++ y)
                    _ -> throwError $ TypeError $ "got wrong number of args for plus"
            )),
            ("mult", (\args -> case args of
                    [(Number, x), (Number, y)] -> return $ (Number, x ++ " * " ++ y)
                    _ -> throwError $ TypeError $ "got wrong number of args for mult"
            )),
            ("cipherlen", (\args -> case args of
                    [(_,x)] -> do
                        tsz <- useAeadTagSize
                        return $ (Number, x ++ " + " ++ show tsz)
                    _ -> throwError $ TypeError $ "got wrong number of args for cipherlen"
            )),
            ("is_group_elem", (\args -> case args of
                    [x] -> return $ (Bool, printOwlOp "owl_is_group_elem" [x])
                    _ -> throwError $ TypeError $ "got wrong number of args for is_group_elem"
            )),
            ("concat", (\args -> case args of
                    [x, y] -> return $ (VecU8, printOwlOp "owl_concat" [x, y])
                    _ -> throwError $ TypeError $ "got wrong number of args for concat"
            )),
            ("crh", (\args -> case args of
                    [x] -> return $ (Rc VecU8, printOwlOp "owl_crh" [x])
                    _ -> throwError $ TypeError $ "got wrong number of args for crh"
            )),
            -- ("xor", (VecU8, \args -> case args of
            --     [(_,x), (ADT _,y)] -> return $ x ++ ".owl_xor(&" ++ y ++ ".0[..])"
            --     [(_,x), (_,y)] -> return $ x ++ ".owl_xor(&" ++ y ++ ")"
            --     _ -> throwError $ TypeError $ "got wrong args for xor"
            -- )),
            ("andb", (\args -> case args of
                [(Bool,x), (Bool,y)] -> return $ (Bool, x ++ " && " ++ y)
                _ -> throwError $ TypeError $ "got wrong args for andb"
            ))
        ] 

initEnv :: Flags -> String -> TB.Map String TB.UserFunc -> Env
initEnv flags path userFuncs = Env flags path defaultCipher defaultHMACMode userFuncs initFuncs M.empty S.empty initTypeLayouts initLenConsts M.empty M.empty M.empty S.empty 0 Nothing [] [] M.empty

lookupTyLayout' :: String -> ExtractionMonad (Maybe Layout)
lookupTyLayout' n = do
    ls <- use typeLayouts
    return $ ls M.!? n

lookupTyLayout :: String -> ExtractionMonad Layout
lookupTyLayout n = do
    o <- lookupTyLayout' n
    case o of
        Just l -> return l
        Nothing -> do
            ls <- use typeLayouts
            debugPrint $ "failed lookupTyLayout: " ++ n ++ " in " ++ show (M.keys ls)
            throwError $ UndefinedSymbol n

lookupNameLayout :: NameExp -> ExtractionMonad Layout
lookupNameLayout n = do
    n' <- flattenNameExp n
    o <- lookupTyLayout' n'
    case o of
        Just l -> return l
        Nothing -> do
            case n ^. val of
                NameConst _ p (Just (_, i)) -> do
                    owlName <- flattenPath p
                    os <- use oracles
                    case os M.!? owlName of
                        Just (_, sliceMap) -> do
                            case sliceMap M.!? i of
                                Just (_, _, l) -> return l
                                Nothing -> throwError $ UndefinedSymbol n'
                        Nothing -> throwError $ UndefinedSymbol n'
                _ -> do
                    ls <- use typeLayouts
                    debugPrint $ "failed lookupNameLayout: " ++ n' ++ " in " ++ show (M.keys ls)
                    throwError $ UndefinedSymbol n'


lookupFunc :: Path -> ExtractionMonad (Maybe ([(RustTy, String)] -> ExtractionMonad (RustTy, String)))
lookupFunc fpath = do
    fs <- use funcs
    f <- tailPath fpath
    -- debugPrint $ owlpretty "lookup" <+> pretty f <+> pretty "in" <+> pretty (M.keys fs)
    return $ fs M.!? f
    
lookupStruct :: String -> ExtractionMonad [(String, RustTy)]
lookupStruct s = do
    ss <- use structs
    case ss M.!? s of
        Just fs -> return fs
        Nothing -> throwError $ TypeError $ "struct not found: " ++ s

lookupAdtFunc :: String -> ExtractionMonad (Maybe (String, RustTy, Bool, [(RustTy, String)] -> ExtractionMonad String))
lookupAdtFunc fn = do
    ufs <- use owlUserFuncs
    adtfs <- use adtFuncs
    -- debugPrint $ owlpretty "lookupAdtFunc of" <+> owlpretty fn <+> owlpretty "in" <+> owlpretty ufs
    case lookup fn ufs of
        -- special handling for struct constructors, since their names are path-scoped
        Just (TB.StructConstructor _) -> return $ adtfs M.!? fn 
        Just (TB.StructProjector _ p) -> return $ adtfs M.!? p
        Just (TB.EnumConstructor _ c) -> return $ adtfs M.!? c
        Just _ -> return Nothing-- throwError $ ErrSomethingFailed $ "Unsupported owl user func: " ++ show fn
        Nothing -> return Nothing

lookupUserFunc :: String -> ExtractionMonad (Maybe OwlFunDef)
lookupUserFunc fn = do
    ufs <- use owlUserFuncs
    case lookup fn ufs of
        Just (TB.FunDef b) -> return $ Just b
        _ -> return Nothing

flattenNameExp :: NameExp -> ExtractionMonad String
flattenNameExp n = case n ^. val of
  NameConst _ s _ -> do
      p <- flattenPath s
      return $ rustifyName p
  _ -> throwError $ UnsupportedNameExp n


rustifyArgTy :: CTy -> ExtractionMonad RustTy
rustifyArgTy (CTOption ct) = do
    rt <- rustifyArgTy ct
    return $ Option rt
rustifyArgTy (CTConst p) = do
    n <- flattenPath p
    l <- lookupTyLayout . rustifyName $ n
    return $ case l of
        LBytes _ -> Rc VecU8
        LUnboundedBytes -> Rc VecU8
        LStruct s _ -> ADT s
        LEnum s _ -> ADT s
rustifyArgTy CTBool = return Bool
rustifyArgTy CTUnit = return Unit
rustifyArgTy _ = return $ Rc VecU8

rustifyRetTy :: CTy -> ExtractionMonad RustTy
rustifyRetTy (CTOption ct) = do
    rt <- rustifyArgTy ct
    return $ Option rt
rustifyRetTy (CTConst p) = do
    n <- flattenPath p
    l <- lookupTyLayout . rustifyName $ n
    return $ case l of
        LBytes _ -> Rc VecU8
        LUnboundedBytes -> Rc VecU8
        LStruct s _ -> ADT s
        LEnum s _ -> ADT s
rustifyRetTy CTBool = return Bool
rustifyRetTy CTUnit = return Unit
rustifyRetTy _ = return $ Rc VecU8

-- For computing data structure members
specDataTyOf :: RustTy -> SpecTy
specDataTyOf VecU8 = SpecSeqU8
specDataTyOf Bool = SpecBool
specDataTyOf Number = SpecNumber
specDataTyOf String = SpecString
specDataTyOf Unit = SpecUnit
specDataTyOf (ADT s) = SpecADT (specName . unrustifyName $ s)
specDataTyOf (Option rt) = SpecOption (specDataTyOf rt)
specDataTyOf (Rc rt) = specDataTyOf rt

rustifySpecDataTy :: CTy -> ExtractionMonad SpecTy
rustifySpecDataTy ct = do
    rt <- rustifyArgTy ct
    return $ specDataTyOf rt

specTyOf :: RustTy -> SpecTy
specTyOf (ADT s) = SpecSeqU8 -- in itree specs, everything is maintained as Seq<u8>
specTyOf (Option rt) = SpecOption (specTyOf rt)
specTyOf (Rc rt) = specTyOf rt
specTyOf r = specDataTyOf r

rustifySpecTy :: CTy -> ExtractionMonad SpecTy
rustifySpecTy ct = do
    rt <- rustifyArgTy ct
    return $ specTyOf rt

rcClone :: OwlDoc
rcClone = owlpretty "Rc::clone"

rcNew :: OwlDoc
rcNew = owlpretty "Rc::new"

getCurRetTy :: ExtractionMonad String
getCurRetTy = do
    t <- use curRetTy
    case t of      
        Nothing -> throwError $ ErrSomethingFailed "getCurRetTy of Nothing"
        Just s -> return s

viewVar :: RustTy -> String -> String
viewVar VecU8 s = s ++ ".view()"
viewVar Bool s = s
viewVar Number s = s
viewVar String s = s
viewVar Unit s = s
viewVar (ADT _) s = s ++ ".view()" -- TODO nesting?
viewVar (Option rt) s = s ++ ".view()"
viewVar (Rc rt) s = viewVar rt s

hexStringToByteList :: String -> ExtractionMonad OwlDoc
hexStringToByteList [] = return $ owlpretty ""
hexStringToByteList (h1 : h2 : t) = do
    t' <- hexStringToByteList t
    return $ owlpretty "0x" <> owlpretty h1 <> owlpretty h2 <> owlpretty "u8," <+> t'
hexStringToByteList _ = throwError OddLengthHexConst

resolveANF :: M.Map String (a, Maybe AExpr) -> AExpr -> ExtractionMonad AExpr
resolveANF binds a = do
    case a^.val of
        AEVar s x -> do 
            case binds M.!? (rustifyName . show $ x) of
                Nothing -> throwError $ ErrSomethingFailed $ "resolveANF failed on: " ++ show x ++ ", " ++ show s 
                Just (_, ianf) -> 
                    case ianf of 
                    Nothing -> return a
                    Just a' -> resolveANF binds a'
        AEApp f ps args -> do
            args' <- mapM (resolveANF binds) args
            return $ mkSpanned $ AEApp f ps args'
        AEHex _ -> return a
        AEPreimage f ps args -> do
            args' <- mapM (resolveANF binds) args
            return $ mkSpanned $ AEPreimage f ps args'
        AEGet _ -> return a
        AEGetEncPK _ -> return a
        AEGetVK _ -> return a
        AEPackIdx i a2 -> do
            a2' <- resolveANF binds a2
            return $ mkSpanned $ AEPackIdx i a2'
        AELenConst _ -> return a
        AEInt _ -> return a


lookupStringAExprMap :: [((String, [AExpr]), a)] -> (String, [AExpr]) -> Maybe a
lookupStringAExprMap [] (n, args) = Nothing
lookupStringAExprMap (((ln, largs), r) : tl) (n, args) =
    if n == ln && all (uncurry aeq) (zip args largs)
    then Just r
    else lookupStringAExprMap tl (n, args)

lookupHashCall :: (String, [AExpr]) -> ExtractionMonad (Maybe (RustTy, String))
lookupHashCall k = do
    hcs <- use hashCalls
    return $ lookupStringAExprMap hcs k

lookupAdtCall :: (String, [AExpr]) -> ExtractionMonad (Maybe (RustTy, String))
lookupAdtCall k = do
    adtcs <- use adtCalls
    return $ lookupStringAExprMap adtcs k