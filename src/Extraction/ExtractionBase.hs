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

instance Pretty RustTy where
  pretty VecU8 = pretty "Vec<u8>"
  pretty RcVecU8 = pretty "Rc<Vec<u8>>"
  pretty Bool = pretty "bool"
  pretty Number = pretty "usize" --should just work
  pretty String = pretty "String"
  pretty Unit = pretty "()"
  pretty (ADT s) = pretty s
  pretty (Option r) = pretty "Option" <> angles (pretty r)

data SpecTy = SpecSeqU8 | SpecBool | SpecNumber | SpecString | SpecUnit | SpecADT String | SpecOption SpecTy
    deriving (Show, Eq, Generic, Typeable)

instance Pretty SpecTy where
  pretty SpecSeqU8 = pretty "Seq<u8>"
  pretty SpecBool = pretty "bool"
  pretty SpecNumber = pretty "usize"
  pretty SpecString = pretty "String"
  pretty SpecUnit = pretty "()"
  pretty (SpecADT s) = pretty s
  pretty (SpecOption r) = pretty "Option" <> angles (pretty r)

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
    _oracles :: M.Map String String, -- how to print the output length
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

instance Pretty Layout where
    pretty (LBytes i) = pretty "bytes" <> parens (pretty i)
    pretty (LStruct name fields) = pretty "struct" <+> pretty name <> pretty ":" <+> pretty fields
    pretty (LEnum name cases) = pretty "enum" <+> pretty name <> pretty ":" <+> pretty (M.keys cases)

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
    | UnsupportedSharedIndices String
    | CouldntParseInclude String
    | ErrSomethingFailed String

instance Pretty ExtractionError where
    pretty (CantLayoutType ct) =
        pretty "Can't make a layout for type:" <+> pretty ct
    pretty (TypeError s) =
        pretty "Type error during extraction:" <+> pretty s
    pretty (UndefinedSymbol s) =
        pretty "Undefined symbol: " <+> pretty s
    pretty OutputWithUnknownDestination =
        pretty "Found a call to `output` without a destination specified. For extraction, all outputs must have a destination locality specified."
    pretty (LocalityWithNoMain s) =
        pretty "Locality" <+> pretty s <+> pretty "does not have a defined main function. For extraction, there should be a defined entry point function that must not take arguments: def" <+> pretty s <> pretty "_main () @" <+> pretty s
    pretty (UnsupportedOracleReturnType s) =
        pretty "Oracle" <+> pretty s <+> pretty "does not return a supported oracle return type for extraction."
    pretty (UnsupportedNameExp ne) =
        pretty "Name expression" <+> pretty ne <+> pretty "is unsupported for extraction."
    pretty (UnsupportedNameType nt) =
        pretty "Name type" <+> pretty nt <+> pretty "is unsupported for extraction."
    pretty (UnsupportedDecl s) =
        pretty "Unsupported decl type for extraction:" <+> pretty s
    pretty (UnsupportedSharedIndices s) =
        pretty "Unsupported sharing of indexed name:" <+> pretty s
    pretty (CouldntParseInclude s) =
        pretty "Couldn't parse included file:" <+> pretty s
    pretty (ErrSomethingFailed s) =
        pretty "Extraction failed with message:" <+> pretty s

printErr :: ExtractionError -> IO ()
printErr e = print $ pretty "Extraction error:" <+> pretty e

debugPrint :: Show s => s -> ExtractionMonad ()
debugPrint = liftIO . hPrint stderr

replacePrimes :: String -> String
replacePrimes = map (\c -> if c == '\'' || c == '.' then '_' else c)

replacePrimes' :: Doc ann -> Doc ann
replacePrimes' = pretty . replacePrimes . show

rustifyName :: String -> String
rustifyName s = "owl_" ++ replacePrimes s

rustifyName' :: Doc ann -> Doc ann
rustifyName' = pretty . rustifyName . show

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
        ("owl_enckey", aeadKeySize defaultCipher + aeadNonceSize defaultCipher),
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


-- NB: Owl puts the key first in enc and dec, Rust puts the plaintext/ciphertext first
initFuncs :: M.Map String (RustTy, [(RustTy, String)] -> ExtractionMonad String)
initFuncs = M.fromList [
        ("eq", (Bool, \args -> case args of
                [(Bool, x), (Bool, y)] -> return $ x ++ " == " ++ y
                [(Number, x), (Number, y)] -> return $ x ++ " == " ++ y
                [(String, x), (String, y)] -> return $ x ++ " == " ++ y
                [(Unit, x), (Unit, y)] -> return $ x ++ " == " ++ y
                [(_,x), (_,y)] -> return $ x ++ ".owl_eq(&" ++ y ++ ")"
                _ -> throwError $ TypeError $ "got wrong args for eq"
        )),
        ("dhpk", (RcVecU8, \args -> case args of
                [x] -> do return $ printOwlOp "owl_dhpk" [x] -- return $ x ++ ".owl_dhpk()"
                _ -> throwError $ TypeError $ "got wrong number of args for dhpk"
        )),
        ("dh_combine", (RcVecU8, \args -> case args of
                [pk, sk] -> do return $ printOwlOp "owl_dh_combine" [pk, sk] --  return $ sk ++ ".owl_dh_combine(&" ++ pk ++ ")"
                _ -> throwError $ TypeError $ "got wrong number of args for dh_combine"
        )),
        ("UNIT", (Unit, \_ -> return "()")),
        ("TRUE", (Bool, \_ -> return "true")),
        ("FALSE", (Bool, \_ -> return "false")),
        ("Some", (Option RcVecU8, \args -> case args of
                [(_,x)] -> return $ "Some(" ++ x ++ ")"
                _ -> throwError $ TypeError $ "got wrong number of args for Some"
        )),
        ("None", (Option RcVecU8, \_ -> return "Option::<Rc<Vec<u8>>>::None")),
        ("length", (Number, \args -> case args of
                [(_,x)] -> return $ x ++ ".owl_length()"
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
        ("checknonce", (Bool, \args -> case args of
                [(_,x), (_,y)] -> return $ x ++ ".owl_eq(&" ++ y ++ ")"
                _ -> throwError $ TypeError $ "got wrong args for eq"
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
    return $ fs M.!? f
    

lookupAdtFunc :: String -> ExtractionMonad (Maybe (String, RustTy, [(RustTy, String)] -> ExtractionMonad (Maybe (String, String), String)))
lookupAdtFunc fn = do
    ufs <- use owlUserFuncs
    adtfs <- use adtFuncs
    -- debugPrint $ pretty "lookupAdtFunc of" <+> pretty fn <+> pretty "in" <+> pretty ufs
    case lookup fn ufs of
        -- special handling for struct constructors, since their names are path-scoped
        Just (TB.StructConstructor _) -> return $ adtfs M.!? fn 
        Just (TB.StructProjector _ p) -> return $ adtfs M.!? p
        Just (TB.EnumConstructor _ c) -> return $ adtfs M.!? c
        Just _ -> throwError $ ErrSomethingFailed $ "Unsupported owl user func: " ++ show fn
        Nothing -> return Nothing

flattenNameExp :: NameExp -> ExtractionMonad String
flattenNameExp n = case n ^. val of
  BaseName _ s -> do
      p <- flattenPath s
      return $ rustifyName p


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


rcClone :: Doc ann
rcClone = pretty "rc_clone"

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