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

data RustTy = VecU8 | RcVecU8 | Bool | Number | String | Unit | ADT String | Option RustTy
    deriving (Show, Eq, Generic, Typeable)

instance OwlPretty RustTy where
  owlpretty VecU8 = owlpretty "Vec<u8>"
  owlpretty RcVecU8 = owlpretty "Rc<Vec<u8>>"
  owlpretty Bool = owlpretty "bool"
  owlpretty Number = owlpretty "usize" --should just work
  owlpretty String = owlpretty "String"
  owlpretty Unit = owlpretty "()"
  owlpretty (ADT s) = owlpretty s
  owlpretty (Option r) = owlpretty "Option" <> angles (owlpretty r)

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

data Env = Env {
    _path :: String,
    _aeadCipherMode :: AEADCipherMode,
    _hmacMode :: HMACMode,
    _owlUserFuncs :: [(String, TB.UserFunc)],
    _funcs :: M.Map String (RustTy, [(RustTy, String)] -> ExtractionMonad String), -- return type, how to print
    _adtFuncs :: M.Map String (String, RustTy, [(RustTy, String)] -> ExtractionMonad (Maybe (String, String), String)),
    _specAdtFuncs :: S.Set String,
    _typeLayouts :: M.Map String Layout,
    _lenConsts :: M.Map String Int,
    _enums :: M.Map (S.Set String) String,
    _oracles :: M.Map (String, Int) String, -- how to print the output length
    _includes :: S.Set String, -- files we have included so far
    _freshCtr :: Integer,
    _curRetTy :: Maybe String -- return type of the def currently being extracted (needed for type annotations)
}

data AEADCipherMode = Aes128Gcm | Aes256Gcm | Chacha20Poly1305 deriving (Show, Eq, Generic, Typeable)

data HMACMode = Sha1 | Sha256 | Sha384 | Sha512 deriving (Show, Eq, Generic, Typeable)

defaultCipher :: AEADCipherMode
defaultCipher = Chacha20Poly1305

defaultHMACMode :: HMACMode
defaultHMACMode = Sha512
data Layout =
  LBytes Int -- number of bytes
  | LStruct String [(String, Layout)] -- field, layout
  | LEnum String (M.Map String (Int, Maybe Layout)) -- finite map from tags to (tag byte, layout)
    deriving (Show, Eq, Generic, Typeable)

instance OwlPretty Layout where
    owlpretty (LBytes i) = owlpretty "bytes" <> parens (owlpretty i)
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

debugPrint :: Show s => s -> ExtractionMonad ()
debugPrint = liftIO . hPrint stderr

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

sigKeySize :: Int
sigKeySize = 1219

vkSize :: Int
vkSize = 1219

dhSize :: Int
dhSize = 91

hmacLen :: Int
hmacLen = 64

initLenConsts :: M.Map String Int
initLenConsts = M.fromList [
        ("owl_signature", 256),
        ("owl_enckey", aeadKeySize defaultCipher),
        ("owl_nonce", aeadNonceSize defaultCipher),
        ("owl_mackey", hmacKeySize),
        ("owl_maclen", hmacLen),
        ("owl_pkekey", pkeKeySize),
        ("owl_sigkey", sigKeySize),
        ("owl_vk", vkSize),
        ("owl_DH", dhSize),
        ("owl_tag", 1)
    ]

initTypeLayouts :: M.Map String Layout
initTypeLayouts = M.map LBytes initLenConsts

printOwlArg :: (RustTy, String) -> String
printOwlArg (RcVecU8, s) = "&(*" ++ s ++ ").as_slice()"
printOwlArg (VecU8, s) = "&" ++ s ++ ".as_slice()"
printOwlArg (ADT _, s) = "&(*" ++ s ++ ".data).as_slice()"
printOwlArg (_, s) = s

printOwlOp :: String -> [(RustTy, String)] -> String
printOwlOp op args = op ++ "(" ++ (foldl1 (\acc s -> acc ++ ", " ++ s) . map printOwlArg $ args) ++ ")"


initFuncs :: M.Map String (RustTy, [(RustTy, String)] -> ExtractionMonad String)
initFuncs = 
    let eqChecker = (Bool, \args -> case args of
                                [(Bool, x), (Bool, y)] -> return $ x ++ " == " ++ y
                                [(Number, x), (Number, y)] -> return $ x ++ " == " ++ y
                                [(String, x), (String, y)] -> return $ x ++ " == " ++ y
                                [(Unit, x), (Unit, y)] -> return $ x ++ " == " ++ y
                                [(ADT _,x), (ADT _,y)] -> return $ "rc_vec_eq(&" ++ x ++ ".data, &" ++ y ++ ".data)"
                                [(RcVecU8, x), (RcVecU8, y)] -> return $ "rc_vec_eq(&" ++ x ++ ", &" ++ y ++ ")"
                                [(VecU8, x), (VecU8, y)] -> return $ "vec_eq(&" ++ x ++ ".data, &" ++ y ++ ".data)"
                                _ -> throwError $ TypeError $ "got wrong args for eq"
                        ) 
    in M.fromList [
            ("eq", eqChecker),
            ("checknonce", eqChecker),
            ("dhpk", (RcVecU8, \args -> case args of
                    [x] -> do return $ printOwlOp "owl_dhpk" [x] -- return $ x ++ ".owl_dhpk()"
                    _ -> throwError $ TypeError $ "got wrong number of args for dhpk"
            )),
            ("dh_combine", (RcVecU8, \args -> case args of
                    [pk, sk] -> do return $ printOwlOp "owl_dh_combine" [pk, sk] --  return $ sk ++ ".owl_dh_combine(&" ++ pk ++ ")"
                    _ -> throwError $ TypeError $ "got wrong number of args for dh_combine"
            )),
            ("unit", (Unit, \_ -> return "()")),
            ("true", (Bool, \_ -> return "true")),
            ("false", (Bool, \_ -> return "false")),
            ("Some", (Option RcVecU8, \args -> case args of
                    [(_,x)] -> return $ "Some(" ++ x ++ ")"
                    _ -> throwError $ TypeError $ "got wrong number of args for Some"
            )),
            ("None", (Option RcVecU8, \_ -> return "Option::<Rc<Vec<u8>>>::None")),
            ("length", (Number, \args -> case args of
                    [(RcVecU8,x)] -> return $ "(*" ++ x ++ ").len()"
                    [(_,x)] -> return $ x ++ ".len()"
                    _ -> throwError $ TypeError $ "got wrong number of args for length"
            )),
            ("zero", (Number, \_ -> return "0")),
            ("plus", (Number, \args -> case args of
                    [(_,x), (_,y)] -> return $ x ++ " + " ++ y
                    _ -> throwError $ TypeError $ "got wrong number of args for plus"
            )),
            ("mult", (Number, \args -> case args of
                    [(_,x), (_,y)] -> return $ x ++ " * " ++ y
                    _ -> throwError $ TypeError $ "got wrong number of args for mult"
            )),
            ("cipherlen", (Number, \args -> case args of
                    [(_,x)] -> do
                        tsz <- useAeadTagSize
                        return $ x ++ " + " ++ show tsz
                    _ -> throwError $ TypeError $ "got wrong number of args for cipherlen"
            )),
            ("xor", (VecU8, \args -> case args of
                [(_,x), (ADT _,y)] -> return $ x ++ ".owl_xor(&" ++ y ++ ".0[..])"
                [(_,x), (_,y)] -> return $ x ++ ".owl_xor(&" ++ y ++ ")"
                _ -> throwError $ TypeError $ "got wrong args for xor"
            )),
            ("andb", (Bool, \args -> case args of
                [(_,x), (_,y)] -> return $ x ++ " && " ++ y
                _ -> throwError $ TypeError $ "got wrong args for andb"
            ))
        ] 

initEnv :: String -> TB.Map String TB.UserFunc -> Env
initEnv path userFuncs = Env path defaultCipher defaultHMACMode userFuncs initFuncs M.empty S.empty initTypeLayouts initLenConsts M.empty M.empty S.empty 0 Nothing

lookupTyLayout :: String -> ExtractionMonad Layout
lookupTyLayout n = do
    ls <- use typeLayouts
    case ls M.!? n of
        Just l -> return l
        Nothing -> do
            debugPrint $ "failed lookupTyLayout: " ++ n ++ " in " ++ show (M.keys ls)
            throwError $ UndefinedSymbol n

lookupFunc :: Path -> ExtractionMonad (Maybe (RustTy, [(RustTy, String)] -> ExtractionMonad String))
lookupFunc fpath = do
    fs <- use funcs
    f <- tailPath fpath
    -- debugPrint $ owlpretty "lookup" <+> pretty f <+> pretty "in" <+> pretty (M.keys fs)
    return $ fs M.!? f
    

lookupAdtFunc :: String -> ExtractionMonad (Maybe (String, RustTy, [(RustTy, String)] -> ExtractionMonad (Maybe (String, String), String)))
lookupAdtFunc fn = do
    ufs <- use owlUserFuncs
    adtfs <- use adtFuncs
    -- debugPrint $ owlpretty "lookupAdtFunc of" <+> owlpretty fn <+> owlpretty "in" <+> owlpretty ufs
    case lookup fn ufs of
        -- special handling for struct constructors, since their names are path-scoped
        Just (TB.StructConstructor _) -> return $ adtfs M.!? fn 
        Just (TB.StructProjector _ p) -> return $ adtfs M.!? p
        Just (TB.EnumConstructor _ c) -> return $ adtfs M.!? c
        Just _ -> throwError $ ErrSomethingFailed $ "Unsupported owl user func: " ++ show fn
        Nothing -> return Nothing

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
rustifyArgTy (CTConst (PUnresolvedVar n)) = do
    l <- lookupTyLayout . rustifyName $ show n
    return $ case l of
        LBytes _ -> RcVecU8
        LStruct s _ -> ADT s
        LEnum s _ -> ADT s
rustifyArgTy CTBool = return Bool
rustifyArgTy CTUnit = return Unit
rustifyArgTy _ = return RcVecU8

rustifyRetTy :: CTy -> ExtractionMonad RustTy
rustifyRetTy (CTOption ct) = do
    rt <- rustifyArgTy ct
    return $ Option rt
rustifyRetTy (CTConst (PUnresolvedVar n)) = do
    l <- lookupTyLayout . rustifyName $ show n
    return $ case l of
        LBytes _ -> RcVecU8
        LStruct s _ -> ADT s
        LEnum s _ -> ADT s
rustifyRetTy CTBool = return Bool
rustifyRetTy CTUnit = return Unit
rustifyRetTy _ = return RcVecU8

specTyOf :: RustTy -> SpecTy
specTyOf VecU8 = SpecSeqU8
specTyOf RcVecU8 = SpecSeqU8
specTyOf Bool = SpecBool
specTyOf Number = SpecNumber
specTyOf String = SpecString
specTyOf Unit = SpecUnit
specTyOf (ADT _) = SpecSeqU8 -- TODO nesting?
specTyOf (Option rt) = SpecOption (specTyOf rt)

rustifySpecTy :: CTy -> ExtractionMonad SpecTy
rustifySpecTy ct = do
    rt <- rustifyArgTy ct
    return $ specTyOf rt


rcClone :: OwlDoc
rcClone = owlpretty "rc_clone"

getCurRetTy :: ExtractionMonad String
getCurRetTy = do
    t <- use curRetTy
    case t of      
        Nothing -> throwError $ ErrSomethingFailed "getCurRetTy of Nothing"
        Just s -> return s

viewVar :: RustTy -> String -> String
viewVar VecU8 s = s ++ ".view()"
viewVar RcVecU8 s = s ++ ".view()"
viewVar Bool s = s
viewVar Number s = s
viewVar String s = s
viewVar Unit s = s
viewVar (ADT _) s = s ++ "data.view()" -- TODO nesting?
viewVar (Option rt) s = s ++ ".view()"

hexStringToByteList :: String -> ExtractionMonad OwlDoc
hexStringToByteList [] = return $ owlpretty ""
hexStringToByteList (h1 : h2 : t) = do
    t' <- hexStringToByteList t
    return $ owlpretty "0x" <> owlpretty h1 <> owlpretty h2 <> owlpretty "u8," <+> t'
hexStringToByteList _ = throwError OddLengthHexConst