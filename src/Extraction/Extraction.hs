{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module Extraction where
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
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Name ( Name(Bn, Fn) )
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Unbound.Generics.LocallyNameless.TH
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import AST
import qualified ANFPass as ANF
import ConcreteAST
import System.IO
import qualified Text.Parsec as P
import qualified Parse as OwlP
import System.FilePath (takeFileName, (</>))
import qualified TypingBase as TB
import Debug.Trace

newtype ExtractionMonad a = ExtractionMonad (ReaderT TB.Env (StateT Env (ExceptT ExtractionError IO)) a)
    deriving (Functor, Applicative, Monad, MonadState Env, MonadError ExtractionError, MonadIO, MonadReader TB.Env)

runExtractionMonad :: TB.Env -> Env -> ExtractionMonad a -> IO (Either ExtractionError a)
runExtractionMonad tcEnv env (ExtractionMonad m) = runExceptT . evalStateT (runReaderT m tcEnv) $ env

liftCheck :: TB.Check a -> ExtractionMonad a
liftCheck c = do
    e <- ask
    o <- liftIO $ runExceptT $ runReaderT (TB.unCheck $ local (set TB.tcScope TB.TcGhost) c) e
    case o of 
      Left s -> ExtractionMonad $ lift $ throwError $ ErrSomethingFailed $ "RustifyPath error: " 
      Right i -> return i

-- Number can be any integer type, ADT means one of our struct/enum representations, VecU8 also includes &[u8], [u8; const len], etc
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

data Env = Env {
    _path :: String,
    _aeadCipherMode :: AEADCipherMode,
    _hmacMode :: HMACMode,
    _owlUserFuncs :: [(String, TB.UserFunc)],
    _funcs :: M.Map String (RustTy, [(RustTy, String)] -> ExtractionMonad String), -- return type, how to print
    _adtFuncs :: M.Map String (String, RustTy, [(RustTy, String)] -> ExtractionMonad (Maybe (String, String), String)),
    _typeLayouts :: M.Map String Layout,
    _lenConsts :: M.Map String Int,
    _enums :: M.Map (S.Set String) String,
    _oracles :: M.Map String String, -- how to print the output length
    _includes :: S.Set String, -- files we have included so far
    _freshCtr :: Integer
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
    owlpretty (UnsupportedSharedIndices s) =
        owlpretty "Unsupported sharing of indexed name:" <+> owlpretty s
    owlpretty (CouldntParseInclude s) =
        owlpretty "Couldn't parse included file:" <+> owlpretty s
    owlpretty (ErrSomethingFailed s) =
        owlpretty "Extraction failed with message:" <+> owlpretty s

printErr :: ExtractionError -> IO ()
printErr e = print $ owlpretty "Extraction error:" <+> owlpretty e

debugPrint :: Show s => s -> ExtractionMonad ()
debugPrint = liftIO . hPrint stderr

replacePrimes :: String -> String
replacePrimes = map (\c -> if c == '\'' || c == '.' then '_' else c)

rustifyName :: String -> String
rustifyName s = "owl_" ++ replacePrimes s

rustifyResolvedPath :: ResolvedPath -> String
--rustifyResolvedPath PTop = trace "Top" "Top"
rustifyResolvedPath (PDot (PPathVar OpenPathVar x) s) = trace ("rustifyResolvedPath of OpenPathVar " ++ show x ++ " " ++ s) s
rustifyResolvedPath (PPathVar (ClosedPathVar s) _) = trace ("rustifyResolvedPath of ClosedPathVar " ++ unignore s) $ unignore s
rustifyResolvedPath (PPathVar OpenPathVar s) = trace ("rustifyResolvedPath of OpenPathVar " ++ show s) $ show s
--rustifyResolvedPath (PDot x y) = trace ("PDot " ++ show x ++ " " ++ show y) $ rustifyResolvedPath x ++ "_" ++ y

rustifyResolvedPath PTop = "Top"
-- rustifyResolvedPath (PDot (PPathVar OpenPathVar _) s) = s
-- rustifyResolvedPath (PPathVar (ClosedPathVar s) _) = unignore s
-- rustifyResolvedPath (PPathVar OpenPathVar s) = show s
rustifyResolvedPath (PDot x y) = rustifyResolvedPath x ++ "_" ++ y


tailPath :: Path -> ExtractionMonad String
tailPath (PRes (PDot _ y)) = return y
tailPath p = throwError $ ErrSomethingFailed $ "couldn't do tailPath of path " ++ show p

rustifyPath :: Path -> ExtractionMonad String
-- rustifyPath (PUnresolvedVar s) = show s
rustifyPath (PRes rp) = do
    rp' <- liftCheck $ TB.normResolvedPath rp
    return $ rustifyResolvedPath rp'
rustifyPath p = error $ "bad path: " ++ show p

locName :: String -> String
locName x = "loc_" ++ replacePrimes x

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
        ("dhpk", (VecU8, \args -> case args of
                [(_,x)] -> return $ x ++ ".owl_dhpk()"
                _ -> throwError $ TypeError $ "got wrong number of args for dhpk"
        )),
        ("dh_combine", (VecU8, \args -> case args of
                [(_,pk), (_,sk)] -> return $ sk ++ ".owl_dh_combine(&" ++ pk ++ ")"
                _ -> throwError $ TypeError $ "got wrong number of args for dh_combine"
        )),
        ("UNIT", (Unit, \_ -> return "()")),
        ("TRUE", (Bool, \_ -> return "true")),
        ("FALSE", (Bool, \_ -> return "false")),
        ("Some", (Option VecU8, \args -> case args of
                [(_,x)] -> return $ "Some(" ++ x ++ ")"
                _ -> throwError $ TypeError $ "got wrong number of args for Some"
        )),
        ("None", (Option VecU8, \_ -> return "Option::<Vec<u8>>::None")),
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
initEnv path userFuncs = Env path defaultCipher defaultHMACMode (userFuncs) initFuncs M.empty initTypeLayouts initLenConsts M.empty M.empty S.empty 0

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
      p <- rustifyPath s
      return $ rustifyName p

-------------------------------------------------------------------------------------------
-- Data representation
-- For enums, we reserve the zero tag for failure cases, so the first correct tag is 1

lenLayoutFailure :: Layout -> Int
lenLayoutFailure (LBytes n) = n
lenLayoutFailure (LStruct _ ls) = foldl' (\ len (_,l) -> lenLayoutFailure l + len) 0 ls
lenLayoutFailure (LEnum _ map) = 1 -- just put a zero tag and nothing after it

layoutCTy :: CTy -> ExtractionMonad Layout
layoutCTy CTData = do throwError $ CantLayoutType CTData
layoutCTy (CTDataWithLength aexp) =
    let helper ae =
            case ae^.val of
            AELenConst s -> do
                lookupTyLayout . rustifyName $ s
            AEInt n -> return $ LBytes n
            AEApp fpath _ args -> do
                fn <- tailPath fpath
                case (fn, args) of
                    ("cipherlen", [inner]) -> do
                        tagSz <- useAeadTagSize
                        li <- helper inner
                        case li of
                            (LBytes ni) -> return $ LBytes (ni + tagSz)
                            _ -> throwError $ CantLayoutType (CTDataWithLength aexp)
                    ("plus", [a, b]) -> do
                        la <- helper a
                        lb <- helper b
                        case (la, lb) of
                            (LBytes na, LBytes nb) -> return $ LBytes (na + nb)
                            _ -> throwError $ CantLayoutType (CTDataWithLength aexp)
                    ("mult", [a, b]) -> do
                        la <- helper a
                        lb <- helper b
                        case (la, lb) of
                            (LBytes na, LBytes nb) -> return $ LBytes (na * nb)
                            _ -> throwError $ CantLayoutType (CTDataWithLength aexp)
                    ("zero", _) -> return $ LBytes 0
                    (_, []) -> do
                        lookupTyLayout . rustifyName $ fn -- func name used as a length constant
            _ -> throwError $ CantLayoutType (CTDataWithLength aexp)
    in
    helper aexp
layoutCTy (CTOption ct) = do
    lct <- layoutCTy ct
    return $ LEnum "builtin_option" $ M.fromList [("Some", (1, Just $ lct)), ("None", (2, Just $ LBytes 0))]
layoutCTy (CTConst p) = do
    p' <- rustifyPath p
    lookupTyLayout . rustifyName $ p'
layoutCTy CTBool = return $ LBytes 1 -- bools are one byte 0 or 1
layoutCTy CTUnit = return $ LBytes 1
layoutCTy (CTName n) = do
    lookupTyLayout =<< flattenNameExp n
layoutCTy (CTVK n) = do
    lookupTyLayout =<< flattenNameExp n
layoutCTy (CTDH_PK n) = do
    lookupTyLayout =<< flattenNameExp n
layoutCTy (CTEnc_PK n) = do
    lookupTyLayout =<< flattenNameExp n
layoutCTy (CTSS n n') = throwError $ CantLayoutType (CTSS n n')

layoutStruct :: String -> [(String, CTy)] -> ExtractionMonad Layout
layoutStruct name fields = do
    fieldLayouts <- go fields
    return $ LStruct name fieldLayouts
    where
        go [] = return []
        go ((name, ct):fs) = do
            lct <- layoutCTy ct
            rest <- go fs
            return $ (name, lct):rest

layoutEnum :: String -> M.Map String (Maybe CTy) -> ExtractionMonad Layout
layoutEnum name cases = do
    let (_, casesTagged) = M.mapAccum tagCase 1 cases
    caseLayouts <- mapM layoutCase casesTagged
    return $ LEnum name caseLayouts
    where
        tagCase n c = (n+1, (n, c))
        layoutCase (n, Just ct) = do
            lcto <- case ct of
                CTData -> return Nothing
                _ -> Just <$> layoutCTy ct
            return (n, lcto)
        layoutCase (n, Nothing) = return (n, Just $ LBytes 0)


---------------------------------------------------------------------------------------
-- ADT extraction

genOwlOpsImpl :: String -> OwlDoc
genOwlOpsImpl name = owlpretty
    "impl OwlOps for" <+> owlpretty name <+> (braces . vsep $ map owlpretty [
        "fn owl_output<A: ToSocketAddrs>(&self, dest_addr: &A, ret_addr: &str) -> () { (&self.0[..]).owl_output(dest_addr, ret_addr) }",
        "fn owl_enc(&self, key: &[u8]) -> Vec<u8> { (&self.0[..]).owl_enc(key) }",
        "fn owl_dec(&self, key: &[u8]) -> Option<Vec<u8>> { (&self.0[..]).owl_dec(key) }",
        "fn owl_eq(&self, other: &Self) -> bool { *self.0 == *other.0 }",
        "fn owl_length(&self) -> usize { self.0.len() }",
        "fn owl_mac(&self, key: &[u8]) -> Vec<u8> { (&self.0[..]).owl_mac(key) }",
        "fn owl_mac_vrfy(&self, key: &[u8], value: &[u8]) -> Option<Vec<u8>> { (&self.0[..]).owl_mac_vrfy(key, value) }",
        "fn owl_pkenc(&self, pubkey: &[u8]) -> Vec<u8> { (&self.0[..]).owl_pkenc(pubkey) }",
        "fn owl_pkdec(&self, privkey: &[u8]) -> Vec<u8> { (&self.0[..]).owl_pkdec(privkey) }",
        "fn owl_sign(&self, privkey: &[u8]) -> Vec<u8> { (&self.0[..]).owl_sign(privkey) }",
        "fn owl_vrfy(&self, pubkey: &[u8], signature: &[u8]) -> Option<Vec<u8>> { (&self.0[..]).owl_vrfy(pubkey, signature) } ",
        "fn owl_dh_combine(&self, others_pk: &[u8]) -> Vec<u8> { (&self.0[..]).owl_dh_combine(others_pk) }",
        "fn owl_dhpk(&self) -> Vec<u8> { (&self.0[..]).owl_dhpk() }",
        "fn owl_extract_expand_to_len(&self, salt: &[u8], len: usize) -> Vec<u8> { (&self.0[..]).owl_extract_expand_to_len(salt, len) }",
        "fn owl_xor(&self, other: &[u8]) -> Vec<u8> { (&self.0[..]).owl_xor(other) }"
    ])

extractStruct :: String -> [(String, Ty)] -> ExtractionMonad (OwlDoc)
extractStruct owlName owlFields = do
    let name = rustifyName owlName
    -- liftIO $ print name
    let parsingOutcomeName = name ++ "_ParsingOutcome"
    let typeDef = owlpretty "pub type" <+> owlpretty name <+> owlpretty "= (Rc<Vec<u8>>," <+> owlpretty parsingOutcomeName <> owlpretty ");"
    let fields = map (\(s,t) -> (rustifyName s, doConcretifyTy t)) owlFields
    layout <- layoutStruct name fields
    layoutFields <- case layout of
      LStruct _ fs -> return fs
      _ -> throwError $ ErrSomethingFailed "layoutStruct returned a non-struct layout"
    parsingOutcomeDef <- genStructParsingOutcomeDef parsingOutcomeName layoutFields
    lenValidFnDef <- genLenValidFnDef name layoutFields
    parseFnDef <- genParseFnDef name parsingOutcomeName layout layoutFields
    constructorDef <- genConstructorDef name parsingOutcomeName layout layoutFields
    selectorDefs <- genSelectorDefs name parsingOutcomeName layoutFields
    structFuncs <- mkStructFuncs owlName parsingOutcomeName owlFields
    let owlOpsImpl = genOwlOpsImpl name
    adtFuncs %= M.union structFuncs
    typeLayouts %= M.insert name layout
    return $ vsep $ [typeDef, parsingOutcomeDef, lenValidFnDef, parseFnDef, constructorDef] ++ selectorDefs ++ [owlOpsImpl]
    where
        mkStructFuncs owlName parsingOutcomeName owlFields = return $
            M.fromList $
                -- don't need to check arity
                (owlName, (rustifyName owlName, ADT (rustifyName owlName), \args -> return $ (Nothing, show $
                        owlpretty "construct_" <> (owlpretty . rustifyName) owlName <>
                            (parens . hsep . punctuate comma . map (\(t,a) -> owlpretty "&" <> owlpretty a <> (case t of
                                ADT _ -> owlpretty ".0"
                                _ -> owlpretty ""))
                            $ args)
                        ))) :
                map (\(owlField, _) -> (owlField, (rustifyName owlName, RcVecU8, \args -> do
                    case args of
                      (ADT _, arg) : _ -> do
                        return $ (Nothing, show $
                            owlpretty "Rc::new(get_" <> (owlpretty . rustifyName) owlField <> owlpretty "_" <> (owlpretty . rustifyName) owlName <> parens (owlpretty "&mut" <+> owlpretty arg) <> owlpretty ".to_owned())")
                      (VecU8, arg) : _ -> do
                        return $ (Just (arg, owlName), show $
                            owlpretty "Rc::new(get_" <> (owlpretty . rustifyName) owlField <> owlpretty "_" <> (owlpretty . rustifyName) owlName <>
                                parens (owlpretty "&" <+> owlpretty owlName) <> owlpretty ".to_owned())")
                      (RcVecU8, arg) : _ -> do
                        return $ (Just (arg, owlName), show $
                            owlpretty "Rc::new(get_" <> (owlpretty . rustifyName) owlField <> owlpretty "_" <> (owlpretty . rustifyName) owlName <>
                                parens (owlpretty "&" <+> owlpretty owlName) <> owlpretty ".to_owned())")
                      _ -> throwError $ TypeError $ "attempt to get from " ++ owlName ++ " with bad args"
                ))) owlFields

        genStructParsingOutcomeDef parsingOutcomeName layoutFields = return $
            owlpretty "#[derive(PartialEq, Eq, Debug)]" <> line <>
            owlpretty "pub enum" <+> owlpretty parsingOutcomeName <+>
            vsep [  lbrace,
                    owlpretty "Success" <> parens (hsep $ punctuate comma $ replicate (length layoutFields + 1) $ owlpretty "usize") <> comma,
                    owlpretty "Failure" <> comma,
                    rbrace]

        genLenValidFnDef name layoutFields =
            let fieldCheckers = map fieldChecker layoutFields in
            let startsPrettied = hsep $ punctuate comma (map (\(n,_) -> owlpretty "start_" <> owlpretty n) layoutFields ++ [owlpretty "i"]) in
            return $ owlpretty "pub fn" <+> owlpretty "len_valid_" <> owlpretty name <> parens (owlpretty "arg: &[u8]") <+>
                owlpretty " -> Option" <> (angles . parens . hsep . punctuate comma $ [owlpretty "usize" | _ <- [0..(length layoutFields)]]) <+> lbrace <> line <>
            owlpretty "let mut i = 0;" <> line <>
            vsep fieldCheckers <> line <>
            owlpretty "Some" <> (parens . parens $ startsPrettied) <> line <>
            rbrace
        fieldChecker (n, l) = case l of
            LBytes nb    ->
                owlpretty "let start_" <> owlpretty n <+> owlpretty "= i;" <> line <>
                owlpretty "if" <+> owlpretty "arg.len() - i" <+> owlpretty "<" <+> owlpretty nb <+> lbrace <> line <>
                owlpretty "return None;" <> line <>
                rbrace <> line <>
                owlpretty "i +=" <+> owlpretty nb <> owlpretty ";"
            LStruct sn sfs ->
                owlpretty "let start_" <> owlpretty n <+> owlpretty "= i;" <> line <>
                owlpretty "match" <+> owlpretty "len_valid_" <> owlpretty sn <> parens (owlpretty "&arg[i..]") <+> lbrace <> line <>
                owlpretty "Some" <> (parens . parens . hsep . punctuate comma $ [owlpretty "_" | _ <- [0..(length sfs - 1)]] ++ [owlpretty "l"]) <+> owlpretty "=>" <+> braces (owlpretty "i += l;") <> line <>
                owlpretty "None => " <> braces (owlpretty "return None;") <> line <>
                rbrace
            LEnum en _   ->
                owlpretty "let start_" <> owlpretty n <+> owlpretty "= i;" <> line <>
                owlpretty "match" <+> owlpretty "len_valid_" <> owlpretty en <> parens (owlpretty "&arg[i..]") <+> lbrace <> line <>
                owlpretty "Some(l) => " <> braces (owlpretty "i += l;") <> line <>
                owlpretty "None => " <> braces (owlpretty "return None;") <> line <>
                rbrace

        genParseFnDef name parsingOutcomeName layout layoutFields = return $
            owlpretty "pub fn" <+> owlpretty "parse_into_" <> owlpretty name <> parens (owlpretty "arg: &mut" <+> owlpretty name) <+> lbrace <> line <>
                owlpretty "if arg.1 ==" <+> owlpretty parsingOutcomeName <> owlpretty "::Failure" <+> lbrace <> line <>
                    owlpretty "match len_valid_" <> owlpretty name <> parens (owlpretty "&arg.0[..]") <+> lbrace <> line <>
                    owlpretty "Some" <> (parens . parens . hsep . punctuate comma $ [owlpretty "idx_" <> owlpretty j | j <- [0..(length layoutFields)]]) <+>
                        owlpretty "=>" <+> braces (
                            owlpretty "arg.1 =" <+> owlpretty parsingOutcomeName <> owlpretty "::Success" <>
                                (parens . hsep . punctuate comma $ [owlpretty "idx_" <> owlpretty j | j <- [0..(length layoutFields)]]) <>
                            owlpretty ";"
                        ) <> line <>
                    owlpretty "None => " <> braces (
                            owlpretty "arg.0 =" <+> owlpretty "Rc::new(vec![0;" <+> owlpretty (lenLayoutFailure layout) <> owlpretty "]);" <> line <>
                            owlpretty "arg.1 =" <+> owlpretty parsingOutcomeName <> owlpretty "::Failure;"
                        ) <> line <>
                    rbrace <> line <>
                rbrace <> line <>
            rbrace


        genConstructorDef name parsingOutcomeName layout layoutFields = do
            let argsPrettied = hsep $ punctuate comma $ map (\(n,_) -> owlpretty "arg_" <> owlpretty n <> owlpretty ": &[u8]") layoutFields
            let startsPrettied = hsep $ punctuate comma (map (\(n,_) -> owlpretty "start_" <> owlpretty n) layoutFields ++ [owlpretty "i"])
            let checkAndExtenders = map (\(n,l) -> checkAndExtender (lenLayoutFailure layout) parsingOutcomeName n l) layoutFields
            return $ owlpretty "pub fn" <+> owlpretty "construct_" <> owlpretty name <> parens argsPrettied <+> owlpretty "->" <+> owlpretty name <+> lbrace <> line <>
                owlpretty "let mut v = vec![];" <> line <>
                owlpretty "let mut i = 0;" <> line <>
                vsep checkAndExtenders <> line <>
                owlpretty "let res = (Rc::new(v)," <+> owlpretty parsingOutcomeName <> owlpretty "::Success" <> parens startsPrettied <> owlpretty ");" <> line <>
                owlpretty "res" <> line <>
                rbrace
        checkAndExtender lenFailure parsingOutcomeName n l =
            let structEnumChecker dn = owlpretty "len_valid_" <> owlpretty dn <> parens (owlpretty "arg_" <> owlpretty n) <+> owlpretty " == None" in
            let checker = case l of
                    LBytes i     -> owlpretty "arg_" <> owlpretty n <> owlpretty ".len()" <+> owlpretty "!=" <+> owlpretty i
                    LStruct sn _ -> structEnumChecker sn
                    LEnum en _   -> structEnumChecker en in
            owlpretty "let start_" <> owlpretty n <+> owlpretty "= i;" <> line <>
            owlpretty "if" <+> checker <+> lbrace <> line <>
            owlpretty "return" <+> parens (owlpretty "Rc::new(vec![0;" <+> owlpretty lenFailure <> owlpretty "])," <+> owlpretty parsingOutcomeName <> owlpretty "::Failure") <> owlpretty ";" <> line <>
            rbrace <> line <>
            owlpretty "v.extend" <> parens (owlpretty "arg_" <> owlpretty n) <> owlpretty ";" <> line <>
            owlpretty "i += " <> owlpretty "arg_" <> owlpretty n <> owlpretty ".len();"

        genSelectorDefs name parsingOutcomeName layoutFields = do
            let (_, layoutOffsets) = mapAccumL (\(o,i) (n,l) -> let nextO = o + lenLayoutFailure l in ((nextO, i + 1), (n,l,o,nextO,i))) (0,0) layoutFields
            return $ map (genSelectorDef name parsingOutcomeName (length layoutFields)) layoutOffsets

        genSelectorDef :: String -> String -> Int -> (String, Layout, Int, Int, Int) -> OwlDoc
        genSelectorDef name parsingOutcomeName numFields (fieldName, fieldLayout, failOffset, failNextOffset, structIdx) =
            let success_pattern = owlpretty parsingOutcomeName <> owlpretty "::Success" <> (parens . hsep . punctuate comma $ [owlpretty "idx_" <> owlpretty j | j <- [0..numFields]]) in
            -- return $
            owlpretty "pub fn" <+> owlpretty "get_" <> owlpretty fieldName <> owlpretty "_" <> owlpretty name <> parens (owlpretty "arg: &" <+> owlpretty name) <+> owlpretty "->" <+> owlpretty "&[u8]" <+> lbrace <> line <>
            owlpretty "// parse_into_" <> owlpretty name <> parens (owlpretty "arg") <> owlpretty ";" <> line <>
            owlpretty "match arg.1 {" <> line <>
            success_pattern <+> owlpretty "=>" <+>
                owlpretty "&arg.0[idx_" <> owlpretty structIdx <> owlpretty "..idx_" <> owlpretty (structIdx + 1) <> owlpretty "]," <> line <>
            owlpretty parsingOutcomeName <> owlpretty "::Failure => &arg.0[" <> owlpretty failOffset <> owlpretty ".." <> owlpretty failNextOffset <> owlpretty "]" <> line <>
            owlpretty "}" <> line <>
            owlpretty "}"



extractEnum :: String -> [(String, Maybe Ty)] -> ExtractionMonad (OwlDoc)
extractEnum owlName owlCases' = do
    let owlCases = M.fromList owlCases'
    let name = rustifyName owlName
    let parsingOutcomeName = name ++ "_ParsingOutcome"
    let cases = M.mapKeys rustifyName $ M.map (fmap doConcretifyTy) owlCases
    layout <- layoutEnum name cases
    layoutCases <- case layout of
      LEnum _ cs -> return cs
      _ -> throwError $ ErrSomethingFailed "layoutEnum returned a non enum layout :("
    let tagsComment = owlpretty "//" <+> owlpretty (M.foldlWithKey (\s name (tag,_) -> s ++ name ++ " -> " ++ show tag ++ ", ") "" layoutCases)
    let typeDef = tagsComment <> line <> owlpretty "pub type" <+> owlpretty name <+> owlpretty "= (Rc<Vec<u8>>," <+> owlpretty parsingOutcomeName <> owlpretty ");"
    parsingOutcomeDef <- genEnumParsingOutcomeDef parsingOutcomeName
    lenValidFnDef <- genLenValidFnDef name layoutCases
    parseFnDef <- genParseFnDef name parsingOutcomeName layout
    constructorDefs <- genConstructorDefs name parsingOutcomeName layout layoutCases
    let owlOpsImpl = genOwlOpsImpl name
    enumFuncs <- mkEnumFuncs owlName owlCases
    adtFuncs %= M.union enumFuncs
    typeLayouts %= M.insert name layout
    enums %= M.insert (S.fromList (map fst owlCases')) owlName
    return $ vsep $ [typeDef, parsingOutcomeDef, lenValidFnDef, parseFnDef] ++ constructorDefs ++ [owlOpsImpl]
    where
        mkEnumFuncs owlName owlCases = return $
            M.fromList $
                map (\(owlCase, _) -> (owlCase, (rustifyName owlName, ADT (rustifyName owlName), \args -> return $ (Nothing, show $
                    owlpretty "construct_" <> (owlpretty . rustifyName) owlName <> owlpretty "_" <> (owlpretty . rustifyName) owlCase <>
                        (parens . hsep . punctuate comma . map (\(t,a) -> owlpretty "&" <> owlpretty a <> (case t of
                                ADT _ -> owlpretty ".0"
                                _ -> owlpretty "")) $ args)
                )))) $ M.assocs owlCases

        genEnumParsingOutcomeDef parsingOutcomeName = return $
            owlpretty "#[derive(PartialEq, Eq, Debug)]" <> line <>
            owlpretty "pub enum" <+> owlpretty parsingOutcomeName <+>
            vsep [  lbrace,
                    owlpretty "Success" <> comma,
                    owlpretty "Failure" <> comma,
                    rbrace]

        genLenValidFnDef name layoutCases =
            let caseCheckers = map caseChecker $ M.assocs layoutCases in
            return $ owlpretty "pub fn" <+> owlpretty "len_valid_" <> owlpretty name <> parens (owlpretty "arg: &[u8]") <+>
                owlpretty " -> Option<usize>" <+> lbrace <> line <>
            owlpretty "if arg.len() < 1 { return None; } else " <> line <>
            vsep (punctuate (owlpretty " else ") caseCheckers) <> line <>
            owlpretty "else { return None; }" <> line <>
            rbrace
        caseChecker (t, (n, l)) = case l of
            Just (LBytes nb)    ->
                owlpretty "if arg[0] ==" <+> owlpretty n <+> owlpretty "&&" <+> owlpretty "arg.len() >=" <+> owlpretty (1 + nb) <+>
                braces (owlpretty " return Some(" <+> owlpretty (1 + nb) <> owlpretty "); ")
            Just (LStruct sn sfs) ->
                owlpretty "if arg[0] ==" <+> owlpretty n <+> braces (
                    owlpretty "match" <+> owlpretty "len_valid_" <> owlpretty sn <> parens (owlpretty "&arg[1..]") <+> lbrace <> line <>
                    owlpretty "Some" <> (parens . parens . hsep . punctuate comma $ [owlpretty "_" | _ <- [0..(length sfs - 1)]] ++ [owlpretty "l"]) <+>
                        owlpretty "=>" <+> braces (owlpretty "return Some(1 + l);") <> line <>
                    owlpretty "None => " <> braces (owlpretty "return None;") <> line <>
                    rbrace
                )
            Just (LEnum en _)   ->
                owlpretty "if arg[0] ==" <+> owlpretty n <+> braces (
                    owlpretty "let start_" <> owlpretty n <+> owlpretty "= i;" <> line <>
                    owlpretty "match" <+> owlpretty "len_valid_" <> owlpretty en <> parens (owlpretty "&arg[1..]") <+> lbrace <> line <>
                    owlpretty "Some(l) => " <> braces (owlpretty "return Some(1 + l);") <> line <>
                    owlpretty "None => " <> braces (owlpretty "return None;") <> line <>
                    rbrace
                )
            Nothing ->
                owlpretty "if arg[0] ==" <+> owlpretty n <+> braces ( owlpretty "return Some(arg.len());" )

        genParseFnDef name parsingOutcomeName layout = return $
            owlpretty "pub fn" <+> owlpretty "parse_into_" <> owlpretty name <> parens (owlpretty "arg: &mut" <+> owlpretty name) <+> lbrace <> line <>
                owlpretty "if arg.1 ==" <+> owlpretty parsingOutcomeName <> owlpretty "::Failure" <+> lbrace <> line <>
                    owlpretty "match len_valid_" <> owlpretty name <> parens (owlpretty "&arg.0[..]") <+> lbrace <> line <>
                    owlpretty "Some(l)" <+>
                        owlpretty "=>" <+> braces (owlpretty "arg.1 =" <+> owlpretty parsingOutcomeName <> owlpretty "::Success;") <> line <>
                    owlpretty "None => " <> braces (
                            owlpretty "arg.0 =" <+> owlpretty "Rc::new(vec![0;" <+> owlpretty (lenLayoutFailure layout) <> owlpretty "]);" <> line <>
                            owlpretty "arg.1 =" <+> owlpretty parsingOutcomeName <> owlpretty "::Failure;"
                        ) <> line <>
                    rbrace <> line <>
                rbrace <> line <>
            rbrace

        genConstructorDefs name parsingOutcomeName layout layoutCases =
            return $ map (genConstructorDef name parsingOutcomeName) $ M.assocs layoutCases

        genConstructorDef :: String -> String -> (String, (Int, Maybe Layout)) -> OwlDoc
        genConstructorDef name parsingOutcomeName (tagName, (tag, Just (LBytes 0))) = -- special case for a case with no payload, where the constructor takes no arg
            owlpretty "pub fn" <+> owlpretty "construct_" <> owlpretty name <> owlpretty "_" <> owlpretty tagName <> owlpretty "()" <+> owlpretty "->" <+> owlpretty name <+> lbrace <> line <>
                owlpretty "let mut v = vec![" <> owlpretty tag <> owlpretty "u8];" <> line <>
                owlpretty "let res = (Rc::new(v)," <+> owlpretty parsingOutcomeName <> owlpretty "::Success" <> owlpretty ");" <> line <>
                owlpretty "res" <> line <>
            rbrace

        genConstructorDef name parsingOutcomeName (tagName, (tag, tagLayout)) =
            -- Failure case for struct is always a zero tag with no payload
            let failureReturn = owlpretty "return" <+> parens (owlpretty "Rc::new(vec![0; 1])," <+> owlpretty parsingOutcomeName <> owlpretty "::Failure") <> owlpretty ";" in
            let checkAndExtender = case tagLayout of
                    Just (LBytes nb)    ->
                        owlpretty "if" <+> owlpretty "arg.len()" <+> owlpretty "<" <+> owlpretty nb <+> braces failureReturn <> line <>
                        owlpretty "v.extend" <> parens (owlpretty "&arg[.." <> owlpretty nb <> owlpretty "]") <> owlpretty ";" <> line
                    Just (LStruct sn sfs) ->
                        owlpretty "match" <+> owlpretty "len_valid_" <> owlpretty sn <> parens (owlpretty "arg") <+> lbrace <> line <>
                        owlpretty "Some" <> (parens . parens . hsep . punctuate comma $ [owlpretty "_" | _ <- [0..(length sfs - 1)]] ++ [owlpretty "l"]) <+>
                            owlpretty "=>" <+> braces (owlpretty "v.extend" <> parens (owlpretty "&arg[..l]") <> owlpretty ";") <> line <>
                        owlpretty "None => " <> braces failureReturn <> line <>
                        rbrace
                    Just (LEnum en _)   ->
                        owlpretty "match" <+> owlpretty "len_valid_" <> owlpretty en <> parens (owlpretty "arg") <+> lbrace <> line <>
                        owlpretty "Some(l) => " <> braces (owlpretty "v.extend" <> parens (owlpretty "&arg[..l]") <> owlpretty ";") <> line <>
                        owlpretty "None => " <> braces failureReturn <> line <>
                        rbrace
                    Nothing ->
                        owlpretty "v.extend(&arg[..]);"
                in
            owlpretty "pub fn" <+> owlpretty "construct_" <> owlpretty name <> owlpretty "_" <> owlpretty tagName <> parens (owlpretty "arg: &[u8]") <+> owlpretty "->" <+> owlpretty name <+> lbrace <> line <>
                owlpretty "let mut v = vec![" <> owlpretty tag <> owlpretty "u8];" <> line <>
                checkAndExtender <> line <>
                owlpretty "let res = (Rc::new(v)," <+> owlpretty parsingOutcomeName <> owlpretty "::Success" <> owlpretty ");" <> line <>
                owlpretty "res" <> line <>
            rbrace

-------------------------------------------------------------------------------------------
-- Code generation

extractCryptOp :: M.Map String RustTy -> CryptOp -> [AExpr] -> ExtractionMonad (RustTy, OwlDoc, OwlDoc)
extractCryptOp binds op owlArgs = do
    argsPretties <- mapM (extractAExpr binds . view val) owlArgs
    let preArgs = foldl (\p (_,s,_) -> p <> s) (owlpretty "") argsPretties
    let args = map (\(r, _, p) -> (r, show p)) argsPretties
    (rt, str) <- case (op, args) of
        (CHash _ i, [(_,x)]) -> error "unimp" 
        --    roname <- rustifyPath p 
        --    orcls <- use oracles
        --    case orcls M.!? roname of
        --        Nothing -> throwError $ TypeError "unrecognized random oracle"
        --        Just outLen -> do
        --            return (VecU8, x ++ ".owl_extract_expand_to_len(&self.salt, " ++ outLen ++ ")")
        (CPRF s, _) -> do throwError $ ErrSomethingFailed $ "TODO implement crypto op: " ++ show op
        (CAEnc, [(_,k), (_,x)]) -> do return (VecU8, x ++ ".owl_enc(&" ++ k ++ ")")
        (CADec, [(_,k), (_,x)]) -> do return (Option VecU8, x ++ ".owl_dec(&" ++ k ++ ")")
        (CEncStAEAD p (sids, pids), _) -> do throwError $ ErrSomethingFailed $ "TODO implement crypto op: " ++ show op
        (CDecStAEAD, _) -> do throwError $ ErrSomethingFailed $ "TODO implement crypto op: " ++ show op
        (CPKEnc, [(_,k), (_,x)]) -> do return (VecU8, x ++ ".owl_pkenc(&" ++ k ++ ")")
        (CPKDec, [(_,k), (_,x)]) -> do return (VecU8, x ++ ".owl_pkdec(&" ++ k ++ ")")
        (CMac, [(_,k), (_,x)]) -> do return (VecU8, x ++ ".owl_mac(&" ++ k ++ ")")
        (CMacVrfy, [(_,k), (_,x), (_,v)]) -> do return (Option VecU8, x ++ ".owl_mac_vrfy(&" ++ k ++ ", &" ++ v ++ ")")
        (CSign, [(_,k), (_,x)]) -> do return (VecU8, x ++ ".owl_sign(&" ++ k ++ ")")
        (CSigVrfy, [(_,k), (_,x), (_,v)]) -> do return (Option VecU8, x ++ ".owl_vrfy(&" ++ k ++ ", &" ++ v ++ ")")
        (_, _) -> do throwError $ TypeError $ "got bad args for crypto op: " ++ show op ++ "(" ++ show args ++ ")"
    return (rt, preArgs, owlpretty str)


extractAExpr :: M.Map String RustTy -> AExprX -> ExtractionMonad (RustTy, OwlDoc, OwlDoc)
extractAExpr binds (AEVar _ owlV) = do
    let v = rustifyName . show $ owlV
    case binds M.!? v of
      Nothing -> do
        debugPrint $ "failed to find " ++ show v ++ " in binds: " ++ show binds
        return (VecU8, owlpretty "", owlpretty v)
      Just RcVecU8 -> return (RcVecU8, owlpretty "", owlpretty "Rc::clone" <> parens (owlpretty "&" <> owlpretty v))
      Just rt -> return (rt, owlpretty "", owlpretty v)
extractAExpr binds (AEApp owlFn fparams owlArgs) = do
    fs <- use funcs
    argsPretties <- mapM (extractAExpr binds . view val) owlArgs
    let preArgs = foldl (\p (_,s,_) -> p <> s) (owlpretty "") argsPretties
    let args = map (\(r, _, p) -> (r, show p)) argsPretties
    fdef <- lookupFunc owlFn
    case fdef of
        Just (rt, f) -> do
            str <- f args
            return (rt, preArgs, owlpretty str)
        Nothing -> do
            -- adtfs <- use adtFuncs
            adtf <- lookupAdtFunc =<< rustifyPath owlFn
            case adtf of
                Just (adt, rt, f) -> do
                    (argvaropt, str) <- f args
                    let s = case argvaropt of
                            Nothing -> owlpretty ""
                            Just (arg,var) ->
                                owlpretty "let mut" <+> owlpretty var <+> owlpretty "=" <+> parens (owlpretty arg <> comma <+> owlpretty adt <> owlpretty "_ParsingOutcome::Failure") <> owlpretty ";" <> line <>
                                owlpretty "parse_into_" <> owlpretty adt <> parens (owlpretty "&mut" <+> owlpretty var) <> owlpretty ";"
                    return (rt, preArgs <> s, owlpretty str)
                Nothing ->
                    if owlFn `aeq` (PUnresolvedVar $ "H") then
                        -- special case for the random oracle function
                        let unspanned = map (view val) owlArgs in
                        case (fparams, unspanned) of
                            ([ParamStr roname], [AEVar owlV _]) -> do
                                orcls <- use oracles
                                case orcls M.!? roname of
                                    Nothing -> throwError $ TypeError "unrecognized random oracle"
                                    Just outLen -> do
                                        return (VecU8, owlpretty "", (owlpretty . rustifyName . unignore $ owlV) <>
                                                                owlpretty ".owl_extract_expand_to_len(&self.salt," <+> owlpretty outLen <> owlpretty ")")
                            _ -> throwError $ TypeError $ "incorrect args/params to random oracle function"
                    else throwError $ UndefinedSymbol $ show owlFn
extractAExpr binds (AEHex s) = error "umimp" -- return (VecU8, owlpretty "", dquotes (owlpretty s) <> owlpretty ".as_bytes()")
extractAExpr binds (AEInt n) = return (Number, owlpretty "", owlpretty n)
extractAExpr binds (AEGet nameExp) =
    case nameExp ^. val of
        NameConst ([], _) s Nothing -> do
            fnameExp <- flattenNameExp nameExp
            return (RcVecU8, owlpretty "", owlpretty "Rc::clone" <> parens (owlpretty "&self." <> owlpretty (fnameExp)))
        NameConst (sidxs, _) s Nothing -> do
            ps <- rustifyPath s
            return (RcVecU8, owlpretty "", owlpretty "self.get_" <> owlpretty (rustifyName ps) <> tupled (map (owlpretty . sidName . show . owlpretty) sidxs))
        _ -> throwError $ UnsupportedNameExp nameExp
extractAExpr binds (AEGetEncPK nameExp) = do
    fnameExp <- flattenNameExp nameExp
    return (RcVecU8, owlpretty "", owlpretty "Rc::clone" <> parens (owlpretty "&self.pk_" <> owlpretty fnameExp))
extractAExpr binds (AEGetVK nameExp) = do
    fnameExp <- flattenNameExp nameExp
    return (RcVecU8, owlpretty "", owlpretty "Rc::clone" <> parens (owlpretty "&self.pk_" <> owlpretty fnameExp))
extractAExpr binds (AEPackIdx idx ae) = extractAExpr binds (ae^.val)
extractAExpr binds (AELenConst s) = do
    lcs <- use lenConsts
    case lcs M.!? (rustifyName s) of
      Nothing -> throwError $ UndefinedSymbol s
      Just n -> return (Number, owlpretty "", owlpretty n)



extractExpr :: Locality -> M.Map String RustTy -> CExpr -> ExtractionMonad (M.Map String RustTy, RustTy, OwlDoc, OwlDoc)
extractExpr loc binds CSkip = return (binds, Unit, owlpretty "", owlpretty "()")
extractExpr loc binds (CInput xsk) = do
    let ((x, ev), k) = unsafeUnbind xsk
    let rustX = rustifyName . show $ x
    let rustEv = if show ev == "_" then "_" else rustifyName . show $ ev
    (_, rt', prek, kPrettied) <- extractExpr loc (M.insert rustX RcVecU8 binds) k
    let eWrapped = owlpretty "Rc::new" <> parens (owlpretty "temp_" <> owlpretty rustX)
    let letbinding =
            owlpretty "let" <+> parens (owlpretty "temp_" <> owlpretty rustX <> comma <+> owlpretty rustEv) <+> owlpretty "=" <+> owlpretty "owl_input(&self.listener)" <> owlpretty ";" <> line <>
            owlpretty "let" <+> owlpretty rustX <+> owlpretty "=" <+> eWrapped <> owlpretty ";"
    return (binds, rt', owlpretty "", vsep [letbinding, prek, kPrettied])
extractExpr (Locality myLname myLidxs) binds (COutput ae lopt) = do
    (_, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    l <- case lopt of
        Nothing -> throwError OutputWithUnknownDestination
        Just (EndpointLocality (Locality lname _)) -> do
            plname <- rustifyPath lname
            return $ owlpretty "&" <> owlpretty plname <> owlpretty "_addr"
        Just (Endpoint ev) -> return $ owlpretty "&" <> (owlpretty . rustifyName . show $ ev)
    pmyLname <- rustifyPath myLname
    return $ (binds, Unit, preAe, owlpretty "&" <> aePrettied <> owlpretty ".owl_output" <> parens (l <> comma <+> owlpretty "&" <> owlpretty (pmyLname) <> owlpretty "_addr") <> owlpretty ";")
extractExpr loc binds (CLet e xk) = do
    let (x, k) = unsafeUnbind xk
    let rustX = rustifyName . show $ x
    (_, rt, preE, ePrettied) <- extractExpr loc binds e
    (_, rt', preK, kPrettied) <- extractExpr loc (M.insert rustX (if rt == VecU8 then RcVecU8 else rt) binds) k
    let eWrapped = case rt of
            VecU8 -> owlpretty "Rc::new" <> parens (owlpretty "temp_" <> owlpretty rustX)
            RcVecU8 -> owlpretty "Rc::clone" <> parens (owlpretty "&temp_" <> owlpretty rustX)
            _ -> owlpretty "temp_" <> owlpretty rustX
    let letbinding = case e of
            CSkip -> owlpretty ""
            _ -> owlpretty "let" <+> owlpretty "temp_" <> owlpretty rustX <+> owlpretty "=" <+> lbrace <+> ePrettied <+> rbrace <> owlpretty ";" <> line <>
                 owlpretty "let" <+> owlpretty rustX <+> owlpretty "=" <+> eWrapped <> owlpretty ";"
    return (binds, rt', owlpretty "", vsep [preE, letbinding, preK, kPrettied])
extractExpr loc binds (CIf ae eT eF) = do
    (_, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    (_, rt, preeT, eTPrettied) <- extractExpr loc binds eT
    (_, rt', preeF, eFPrettied) <- extractExpr loc binds eF
    return (binds, rt, owlpretty "", preAe <> line <> owlpretty "if" <+> aePrettied <+> braces (vsep [preeT, eTPrettied]) <+> owlpretty "else" <+> braces (vsep [preeF, eFPrettied]))
extractExpr loc binds (CRet ae) = do
    (rt, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    return (binds, rt, preAe, aePrettied)
extractExpr loc binds (CCall owlFn (sids, pids) owlArgs) = do
    fs <- use funcs
    argsPretties <- mapM (extractAExpr binds . view val) owlArgs
    let preArgs = foldl (\p (_,s,_) -> p <> s) (owlpretty "") argsPretties
    let args = map (\sid -> (Number, sidName . show . owlpretty $ sid)) sids ++ map (\(r, _, p) -> (r, show p)) argsPretties
    powlFn <- rustifyPath owlFn
    case fs M.!? (powlFn) of
      Nothing -> do
        throwError $ UndefinedSymbol (powlFn)
      Just (rt, f) -> do
        str <- f args
        return (binds, rt, preArgs, owlpretty str)
extractExpr loc binds (CCase ae cases) = do
   (rt, preAe, aePrettied) <- extractAExpr binds $ ae^.val
   case rt of
     Option rt' -> do
       casesPrettiedRts <- forM cases $ \(c, o) ->
               case o of
                   Left e -> do
                       (_, rt'', preE, ePrettied) <- extractExpr loc binds e
                       return (rt'', owlpretty c <+> owlpretty "=>" <+> braces (vsep [preE, ePrettied]))
                   Right xk -> do
                       let (x, k) = unsafeUnbind xk
                       let rustX = rustifyName . show $ x
                       (_, rt'', preK, kPrettied) <- extractExpr loc (M.insert rustX (if rt' == VecU8 then RcVecU8 else rt') binds) k
                       let eWrapped = case rt' of
                               VecU8 -> owlpretty "Rc::new" <> parens (owlpretty "temp_" <> owlpretty rustX)
                               RcVecU8 -> owlpretty "Rc::clone" <> parens (owlpretty "&temp_" <> owlpretty rustX)
                               _ -> owlpretty "temp_" <> owlpretty rustX
                       return (rt'', owlpretty c <> parens (owlpretty "temp_" <> owlpretty rustX) <+> owlpretty "=>"
                                   <+> braces (owlpretty "let" <+> owlpretty rustX <+> owlpretty "=" <+> eWrapped <> owlpretty ";" <> line <> preK <> line <> kPrettied))
       branchRt <- case casesPrettiedRts of
         [] -> throwError $ TypeError "case on Option type with no cases"
         (b, _) : _ -> return b
       let casesPrettied = map snd casesPrettiedRts
       return (binds, branchRt, owlpretty "", preAe <> line <> owlpretty "match " <+> aePrettied <+> (braces . vsep $ casesPrettied))
     _ -> do -- We are casing on an Owl ADT
       es <- use enums
       enumOwlName <- case es M.!? (S.fromList (map fst cases)) of
         Nothing -> throwError $ UndefinedSymbol $ "can't find an enum whose cases are " ++ (show . map fst $ cases)
         Just s -> do debugPrint $ owlpretty "enum casing on" <+> owlpretty s; return s
       ts <- use typeLayouts
       enumLayout <- case ts M.!? rustifyName enumOwlName of
         Just (LEnum n c) -> return c
         _ -> throwError $ UndefinedSymbol enumOwlName
       let tagByteOf = \c -> do
               case enumLayout M.!? (rustifyName c) of
                       Nothing -> throwError $ ErrSomethingFailed "enum case not found"
                       Just (b,_) -> return b
       casesPrettiedRts <- forM cases $ \(c, o) ->
               case o of
                   Left e -> do
                       b <- tagByteOf c
                       (_, rt'', preE, ePrettied) <- extractExpr loc binds e
                       return (rt'', owlpretty b <+> owlpretty "=>" <+> braces (vsep [preE, ePrettied]))
                   Right xk -> do
                       b <- tagByteOf c
                       let (x, k) = unsafeUnbind xk
                       let rustX = rustifyName . show $ x
                       (_, rt'', preK, kPrettied) <- extractExpr loc (M.insert rustX RcVecU8 binds) k
                       let eWrapped = owlpretty "Rc::new(caser_tmp.0[1..].to_vec())"
                       return (rt'', owlpretty b <+> owlpretty "=>"
                                   <+> braces (owlpretty "let" <+> owlpretty rustX <+> owlpretty "=" <+> eWrapped <> owlpretty ";" <> line <> preK <> line <> kPrettied))
       branchRt <- case casesPrettiedRts of
         [] -> throwError $ TypeError "case on enum with no cases"
         (b, _) : _ -> return b
       let defaultCase = case branchRt of
             VecU8 -> owlpretty "vec![0]"
             RcVecU8 -> owlpretty "Rc::new(vec![0])"
             Bool -> owlpretty "/* arbitrarily autogenerated */ false"
             Number -> owlpretty "/* arbitrarily autogenerated */ 0"
             String -> owlpretty "/* arbitrarily autogenerated */ \"\""
             Unit -> owlpretty "()"
             ADT s -> owlpretty "{ let mut tmp = (Rc::new(vec![])," <+> owlpretty s <> owlpretty "_ParsingOutcome::Failure); parse_into_" <> owlpretty s <> owlpretty "(&mut tmp); tmp }"
             Option _ -> owlpretty "/* arbitrarily autogenerated */ None"
       let casesPrettied = map snd casesPrettiedRts
       return (binds, branchRt, owlpretty "", preAe <> braces (
               owlpretty "let mut caser_tmp" <+> owlpretty "=" <+> parens (aePrettied <> comma <+> owlpretty (rustifyName enumOwlName) <> owlpretty "_ParsingOutcome::Failure") <> owlpretty ";" <> line <>
               owlpretty "parse_into_" <> owlpretty (rustifyName enumOwlName)  <> parens (owlpretty "&mut caser_tmp") <> owlpretty ";" <> line <>
               owlpretty "match caser_tmp.0[0]" <+> braces (
                   vsep casesPrettied <> line <>
                   owlpretty "_ =>" <+> defaultCase <> comma
               ))
           )
extractExpr loc binds (CTLookup tbl ae) = do
    (rt, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    aeWrapped <- case rt of
            RcVecU8 -> return $ owlpretty "&" <> aePrettied <> owlpretty "[..]"
            VecU8 -> return $ owlpretty "&" <> aePrettied
            _ -> throwError $ ErrSomethingFailed "got wrong arg type for lookup"
    ptbl <- rustifyPath tbl
    let tblName = rustifyName ptbl
    return (binds, Option VecU8, preAe, owlpretty "self." <> owlpretty tblName <> owlpretty ".get" <> parens aeWrapped <> owlpretty ".cloned()")
extractExpr loc binds (CCrypt cryptOp args) = do
    (rt, pre, opPrettied) <- extractCryptOp binds cryptOp args
    return (binds, rt, pre, opPrettied)
extractExpr loc binds c = throwError $ ErrSomethingFailed $ "unimplemented case for extractExpr: " ++ (show . owlpretty $ c)

funcCallPrinter :: String -> [(String, RustTy)] -> [(RustTy, String)] -> ExtractionMonad String
funcCallPrinter name rustArgs callArgs = do
    if length rustArgs == length callArgs then
        return $ show $ owlpretty "self." <> owlpretty name <> (parens . hsep . punctuate comma . map (\(rty, arg) -> (if rty == Number then owlpretty "" else owlpretty "&") <+> owlpretty arg) $ callArgs)
    else throwError $ TypeError $ "got wrong args for call to " ++ name

extractArg :: (String, RustTy) -> OwlDoc
extractArg (s, rt) =
    owlpretty s <> owlpretty ": &" <+> owlpretty rt

rustifyArg :: (DataVar, Embed Ty) -> ExtractionMonad (String, RustTy)
rustifyArg (v, t) = do
    rt <- rustifyArgTy . doConcretifyTy . unembed $ t
    return (rustifyName $ show v, rt)

rustifySidArg :: IdxVar -> (String, RustTy)
rustifySidArg v =
    (sidName . show $ v, Number)

rustifyArgTy :: CTy -> ExtractionMonad RustTy
rustifyArgTy (CTOption ct) = do
    rt <- rustifyArgTy ct
    return $ Option rt
rustifyArgTy (CTConst (PUnresolvedVar n)) = do
    l <- lookupTyLayout . rustifyName $ show n
    return $ case l of
        LBytes _ -> VecU8
        LStruct s _ -> ADT s
        LEnum s _ -> ADT s
rustifyArgTy CTBool = return Bool
rustifyArgTy CTUnit = return Unit
rustifyArgTy _ = return VecU8

makeFunc :: String -> Locality -> [IdxVar] -> [(DataVar, Embed Ty)] -> Ty  -> ExtractionMonad ()
makeFunc owlName _ sidArgs owlArgs owlRetTy = do
    let name = rustifyName owlName
    rustArgs <- mapM rustifyArg owlArgs
    let rustSidArgs = map rustifySidArg sidArgs
    rtb <- rustifyArgTy $ doConcretifyTy owlRetTy
    funcs %= M.insert owlName (rtb, funcCallPrinter name (rustSidArgs ++ rustArgs))
    return ()


extractDef :: String -> Locality -> [IdxVar] -> [(DataVar, Embed Ty)] -> Ty -> Expr -> ExtractionMonad (OwlDoc)
extractDef owlName loc sidArgs owlArgs owlRetTy owlBody = do
    let name = rustifyName owlName
    concreteBody <- ANF.anf owlBody >>= concretify
    -- debugPrint $ "Extracting def " ++ owlName
    -- debugPrint $ owlpretty concreteBody
    rustArgs <- mapM rustifyArg owlArgs
    let rustSidArgs = map rustifySidArg sidArgs
    (_, rtb, preBody, body) <- extractExpr loc (M.fromList rustArgs) concreteBody
    decl <- genFuncDecl name rustSidArgs rustArgs rtb
    return $ decl <+> lbrace <> line <> preBody <> line <> body <> line <> rbrace
    where
        genFuncDecl name sidArgs owlArgs rt = do
            let argsPrettied = 
                    owlpretty "&mut self," 
                    <+> (hsep . punctuate comma . map (\(a,_) -> owlpretty a <+> owlpretty ": usize") $ sidArgs) 
                    <+> (hsep . punctuate comma . map extractArg $ owlArgs)
            return $ owlpretty "pub fn" <+> owlpretty name <> parens argsPrettied <+> owlpretty "->" <+> owlpretty rt


nameInit :: String -> NameType -> ExtractionMonad (OwlDoc)
nameInit s nt = case nt^.val of
    NT_Nonce -> return $ owlpretty "let" <+> owlpretty (rustifyName s) <+> owlpretty "=" <+> owlpretty "owl_aead::gen_rand_nonce(CIPHER);"
    NT_Enc _ -> return $ owlpretty "let" <+> owlpretty (rustifyName s) <+> owlpretty "=" <+> owlpretty "owl_aead::gen_rand_key_iv(CIPHER);"
    NT_MAC _ -> return $ owlpretty "let" <+> owlpretty (rustifyName s) <+> owlpretty "=" <+> owlpretty "owl_hmac::gen_rand_key(&HMAC_MODE);"
    NT_PKE _ -> return $ owlpretty "let" <+> (parens . hsep . punctuate comma . map owlpretty $ [rustifyName s, "pk_" ++ rustifyName s]) <+> owlpretty "=" <+> owlpretty "owl_pke::gen_rand_keys();"
    NT_Sig _ -> return $ owlpretty "let" <+> (parens . hsep . punctuate comma . map owlpretty $ [rustifyName s, "pk_" ++ rustifyName s]) <+> owlpretty "=" <+> owlpretty "owl_pke::gen_rand_keys();"
    NT_DH -> return $ owlpretty "let" <+> (parens . hsep . punctuate comma . map owlpretty $ [rustifyName s, "pk_" ++ rustifyName s]) <+> owlpretty "=" <+> owlpretty "owl_dhke::gen_ecdh_key_pair();"
    _ -> throwError $ ErrSomethingFailed "unimplemented name initializer"


-------------------------------------------------------------------------------------------
-- Handling localities

type LocalityName = String
type NameData = (String, NameType, Int, Int) -- name, type, number of sessionID indices, number of processID indices
type DefData = (String, Locality, [IdxVar], [(DataVar, Embed Ty)], Ty, Expr) -- func name, locality, sessionID arguments, arguments, return type, body
type LocalityData = (Int, [NameData], [NameData], [DefData], [(String, Ty)]) -- number of locality indices, local state, shared state, defs, table names and codomains

preprocessIncludes :: Decl -> ExtractionMonad [Decl]
preprocessIncludes d =
    case d^.val of
        DeclInclude fn -> do
            incs <- use includes
            if S.member fn incs then return []
            else do
                includes %= S.insert fn
                p <- use path
                let fn' = p </> fn
                debugPrint $ "Including decls from " ++ fn'
                s <- liftIO $ readFile fn'
                pres <- liftIO $ P.runParserT OwlP.parseFile () (takeFileName fn') s
                case pres of
                    Left err -> throwError $ CouldntParseInclude $ "parse error: " ++ show err
                    Right dcls -> do
                        preprocessed <- mapM preprocessIncludes dcls
                        return $ concat preprocessed
        d' -> return $ [d]


-- returns (locality stuff, shared names, public keys)
preprocessModBody :: TB.ModBody -> ExtractionMonad (M.Map LocalityName LocalityData, [(NameData, [(LocalityName, Int)])], [NameData])
preprocessModBody mb = do
    let (locs, locAliases) = sortLocs $ mb ^. TB.localities
    let lookupLoc = lookupLoc' locs locAliases
    let locMap = M.map (\npids -> (npids, [],[],[],[])) locs
    locMap <- foldM (sortDef lookupLoc) locMap (mb ^. TB.defs)
    locMap <- foldM (sortTable lookupLoc) locMap (mb ^. TB.tableEnv)
    (locMap, shared, pubkeys) <- foldM (sortName lookupLoc) (locMap, [], []) (mb ^. TB.nameDefs)
    mapM_ processOrcls $ (mb ^. TB.nameDefs)
    -- TODO random oracles, counters
    return (locMap, shared, pubkeys)
    where
        sortLocs = foldl' (\(locs, locAliases) (locName, locType) -> 
                                case locType of 
                                    Left i -> (M.insert locName i locs, locAliases)
                                    Right p -> (locs, M.insert locName (rustifyResolvedPath p) locAliases)) 
                             (M.empty, M.empty)

        lookupLoc' :: M.Map LocalityName Int -> M.Map LocalityName LocalityName -> LocalityName -> ExtractionMonad LocalityName
        lookupLoc' locs locAliases l = do
                case locs M.!? l of
                    Just _ -> return l
                    Nothing -> 
                        case locAliases M.!? l of
                            Just l' -> lookupLoc' locs locAliases l'
                            Nothing -> throwError $ ErrSomethingFailed $ "couldn't lookup locality alias " ++ show l

        sortDef :: (LocalityName -> ExtractionMonad LocalityName) -> M.Map LocalityName LocalityData -> (String, TB.Def) -> ExtractionMonad (M.Map LocalityName LocalityData)
        sortDef _ m (_, TB.DefHeader _) = return m
        sortDef lookupLoc m (owlName, TB.Def idxs_defSpec) = do
                let ((sids, pids), defspec) = unsafeUnbind idxs_defSpec 
                let loc@(Locality locP _) = defspec ^. TB.defLocality
                locName <- lookupLoc =<< rustifyPath locP
                let (args, (_, retTy, body)) = unsafeUnbind (defspec ^. TB.preReq_retTy_body) 
                case body of
                    Nothing -> return m
                    Just e  -> do
                        let f (i, l, s, d, t) = (i, l, s, d ++ [(owlName, loc, sids, args, retTy, e)], t)
                        makeFunc owlName loc sids args retTy
                        return $ M.adjust f locName m
        
        sortTable :: (LocalityName -> ExtractionMonad LocalityName) -> M.Map LocalityName LocalityData -> (String, (Ty, Locality)) -> ExtractionMonad (M.Map LocalityName LocalityData)
        sortTable lookupLoc locMap (name, (ty, Locality locP _)) = do
            locName <- lookupLoc =<< rustifyPath locP
            let f (i, l, s, d, t) = (i, l, s, d, t ++ [(name, ty)])
            return $ M.adjust f locName locMap

        sortName :: (LocalityName -> ExtractionMonad LocalityName) 
                    -> (M.Map LocalityName LocalityData, [(NameData, [(LocalityName, Int)])], [NameData]) 
                    -> (String, (Bind ([IdxVar], [IdxVar]) TB.NameDef))
                    -> ExtractionMonad (M.Map LocalityName LocalityData, [(NameData, [(LocalityName, Int)])], [NameData]) 
        sortName lookupLoc (locMap, shared, pubkeys) (name, binds) = do
            let ((sids, pids), nd) = unsafeUnbind binds
            case nd of
              TB.AbstractName -> return (locMap, shared, pubkeys) -- ignore abstract names, they should be concretized when used
              TB.RODef _ _ -> return (locMap, shared, pubkeys) -- ignore RO defs
              TB.BaseDef (nt, loc) -> do
                nameLen <- case nt ^. val of
                    NT_Nonce -> do useAeadNonceSize
                    NT_Enc _ -> do
                        keySize <- useAeadKeySize
                        ivSize <- useAeadNonceSize
                        return $ keySize + ivSize
                    NT_MAC _ -> do useHmacKeySize
                    NT_PKE _ -> do return pkeKeySize
                    NT_Sig _ -> do return sigKeySize
                    NT_DH -> return dhSize
                    _ -> do
                        throwError $ UnsupportedNameType nt
                let nsids = length sids
                let npids = length pids
                typeLayouts %= M.insert (rustifyName name) (LBytes nameLen)
                let gPub m lo = M.adjust (\(i,l,s,d,t) -> (i, l, s ++ [(name, nt, nsids, npids)], d, t)) lo m
                let gPriv m lo = M.adjust (\(i,l,s,d,t) -> (i, l ++ [(name, nt, nsids, npids)], s, d, t)) lo m
                locNames <- mapM (\(Locality lname _) -> rustifyPath lname) loc
                locNameCounts <- mapM (\(Locality lname lidxs) -> do
                    plname <- rustifyPath lname
                    return (plname, length lidxs)) loc
                case nt ^.val of
                    -- public keys must be shared, so pub/priv key pairs are generated by the initializer
                    NT_PKE _ ->
                        return (foldl gPub locMap locNames, shared ++ [((name, nt, nsids, npids), locNameCounts)], pubkeys ++ [(name, nt, nsids, npids)])
                    NT_Sig _ ->
                        return (foldl gPub locMap locNames, shared ++ [((name, nt, nsids, npids), locNameCounts)], pubkeys ++ [(name, nt, nsids, npids)])
                    NT_DH ->
                        return (foldl gPub locMap locNames, shared ++ [((name, nt, nsids, npids), locNameCounts)], pubkeys ++ [(name, nt, nsids, npids)])
                    _ -> if length loc /= 1 then
                            -- name is shared among multiple localities
                            return (foldl gPub locMap locNames, shared ++ [((name, nt, nsids, npids), locNameCounts)], pubkeys)
                        else
                            -- name is local and can be locally generated
                            return (foldl gPriv locMap locNames, shared, pubkeys)

        processOrcls :: (String, (Bind ([IdxVar], [IdxVar]) TB.NameDef)) -> ExtractionMonad ()
        processOrcls (n, b) = do
            let (_, nd) = unsafeUnbind b
            case nd of
              TB.RODef _ _ -> error "unimp" -- do
                --rtlen <- case (map (view val) rtys) of
                --    [NT_Nonce] -> return "NONCE_SIZE"
                --    [NT_Enc _] -> return "KEY_SIZE + NONCE_SIZE"
                --    _ -> throwError $ UnsupportedOracleReturnType n
                --oracles %= M.insert n rtlen
              _ -> return ()


-- return number of arguments to main and the print of the locality
extractLoc :: [NameData] -> (LocalityName, LocalityData) -> ExtractionMonad (String, Int, OwlDoc)
extractLoc pubKeys (loc, (idxs, localNames, sharedNames, defs, tbls)) = do
    let sfs = stateFields idxs localNames sharedNames pubKeys tbls
    let cfs = configFields idxs sharedNames pubKeys
    indexedNameGetters <- mapM genIndexedNameGetter localNames
    let sharedIndexedNameGetters = map genSharedIndexedNameGetter sharedNames
    case find (\(n,_,sids,as,_,_) -> isSuffixOf "_main" n && null as) defs of
        Just (mainName,_,sids,_,_,_) -> do
            initLoc <- genInitLoc loc localNames sharedNames pubKeys tbls
            fns <- mapM (\(n, l, sids, as, t, e) -> extractDef n l sids as t e) defs
            return (rustifyName mainName, length sids,
                owlpretty "#[derive(Serialize, Deserialize, Debug)]" <> owlpretty "pub struct" <+> owlpretty (locName loc) <> owlpretty "_config" <+> braces cfs <> line <>
                owlpretty "pub struct" <+> owlpretty (locName loc) <+> braces sfs <> line <>
                owlpretty "impl" <+> owlpretty (locName loc) <+> braces (initLoc <+> vsep (indexedNameGetters ++ sharedIndexedNameGetters ++ fns)))
        Nothing -> throwError $ LocalityWithNoMain loc
    where
        genIndexedNameGetter (n, nt, nsids, _) = if nsids == 0 then return $ owlpretty "" else do
            ni <- nameInit n nt
            return $
                owlpretty "pub fn get_" <> owlpretty (rustifyName n) <> tupled (owlpretty "&mut self" : [owlpretty "sid" <> owlpretty n <> owlpretty ": usize" | n <- [0..(nsids-1)]]) <+> owlpretty "-> Rc<Vec<u8>>" <> lbrace <> line <>
                    owlpretty "match self." <> owlpretty (rustifyName n) <> owlpretty ".get" <> parens (tupled ([owlpretty "&sid" <> owlpretty n | n <- [0..(nsids-1)]])) <> lbrace <> line <>
                        owlpretty "Some(v) => Rc::clone(v)," <> line <>
                        owlpretty "None =>" <+> lbrace <> line <>
                            ni <> line <>
                            owlpretty "let v = Rc::new" <> parens (owlpretty (rustifyName n)) <> owlpretty ";" <> line <>
                            owlpretty "self." <> owlpretty (rustifyName n) <> owlpretty ".insert" <> parens (tupled ([owlpretty "sid" <> owlpretty n | n <- [0..(nsids-1)]]) <> comma <+> owlpretty "Rc::clone(&v)") <> owlpretty ";" <> line <>
                            owlpretty "Rc::clone(&v)" <> line <>
                        rbrace <>
                    rbrace <>
                rbrace
        genSharedIndexedNameGetter (n, _, nsids, _) = if nsids == 0 then owlpretty "" else
            owlpretty "pub fn get_" <> owlpretty (rustifyName n) <> tupled (owlpretty "&self" : [owlpretty "sid" <> owlpretty n <> owlpretty ": usize" | n <- [0..(nsids-1)]]) <+> owlpretty "-> Rc<Vec<u8>>" <> lbrace <> line <>
                owlpretty "Rc::clone" <> parens (owlpretty "&self." <> owlpretty (rustifyName n)) <>
            rbrace

        configFields idxs sharedNames pubKeys =
            vsep . punctuate comma $
                map (\(s,_,_,npids) -> owlpretty (rustifyName s) <> (if npids == 0 || (idxs == 1 && npids == 1) then owlpretty ": Vec<u8>" else owlpretty ": HashMap<usize, Vec<u8>>")) sharedNames ++
                map (\(s,_,_,_) -> owlpretty "pk_" <> owlpretty (rustifyName s) <> owlpretty ": Vec<u8>") pubKeys ++
                [owlpretty "salt" <> owlpretty ": Vec<u8>"]
        stateFields idxs localNames sharedNames pubKeys tbls =
            vsep . punctuate comma $
                owlpretty "listener: TcpListener" :
                map (\(s,_,nsids,npids) -> owlpretty (rustifyName s) <>
                        if nsids == 0
                        then owlpretty ": Rc<Vec<u8>>"
                        else owlpretty ": HashMap" <> angles ((tupled [owlpretty "usize" | _ <- [0..(nsids - 1)]]) <> comma <+> owlpretty "Rc<Vec<u8>>")
                    ) localNames ++
                map (\(s,_,_,npids) -> owlpretty (rustifyName s) <> (if npids == 0 || (idxs == 1 && npids == 1) then owlpretty ": Rc<Vec<u8>>" else owlpretty ": Rc<HashMap<usize, Vec<u8>>>")) sharedNames ++
                map (\(s,_,_,_) -> owlpretty "pk_" <> owlpretty (rustifyName s) <> owlpretty ": Rc<Vec<u8>>") pubKeys ++
                -- Tables are always treated as local:
                map (\(n,t) -> owlpretty (rustifyName n) <> owlpretty ": HashMap<Vec<u8>, Vec<u8>>") tbls ++
                [owlpretty "salt" <> owlpretty ": Rc<Vec<u8>>"]
        genInitLoc loc localNames sharedNames pubKeys tbls = do
            localInits <- mapM (\(s,n,i,_) -> if i == 0 then nameInit s n else return $ owlpretty "") localNames
            return $ owlpretty "pub fn init_" <> owlpretty (locName loc) <+> parens (owlpretty "config_path : &str") <+> owlpretty "-> Self" <+> lbrace <> line <>
                owlpretty "let listener = TcpListener::bind" <> parens (owlpretty loc <> owlpretty "_addr") <> owlpretty ".unwrap();" <>
                vsep localInits <> line <>
                owlpretty "let config_str = fs::read_to_string(config_path).expect(\"Config file not found\");" <> line <>
                owlpretty "let config:" <+> owlpretty (locName loc) <> owlpretty "_config =" <+> owlpretty "serde_json::from_str(&config_str).expect(\"Can't parse config file\");" <> line <>
                owlpretty "return" <+> owlpretty (locName loc) <+>
                    braces (hsep . punctuate comma $
                        owlpretty "listener" :
                        map (\(s,_,nsids,_) ->
                                if nsids == 0
                                then (owlpretty . rustifyName $ s) <+> owlpretty ":" <+> owlpretty "Rc::new" <> parens (owlpretty . rustifyName $ s)
                                else (owlpretty . rustifyName $ s) <+> owlpretty ":" <+> owlpretty "HashMap::new()"
                            ) localNames ++
                        map (\(s,_,_,_) -> owlpretty (rustifyName s) <+> owlpretty ":" <+> owlpretty "Rc::new" <> parens (owlpretty "config." <> owlpretty (rustifyName s))) sharedNames ++
                        map (\(s,_,_,_) -> owlpretty "pk_" <> owlpretty (rustifyName s) <+> owlpretty ":" <+> owlpretty "Rc::new" <> parens (owlpretty "config." <> owlpretty "pk_" <> owlpretty (rustifyName s))) pubKeys ++
                        map (\(n,_) -> owlpretty (rustifyName n) <+> owlpretty ":" <+> owlpretty "HashMap::new()") tbls ++
                        [owlpretty "salt : Rc::new(config.salt)"]
                    ) <>
                rbrace

extractLocs :: [NameData] ->  M.Map LocalityName LocalityData -> ExtractionMonad (M.Map LocalityName (String, Int), OwlDoc)
extractLocs pubkeys locMap = do
    let addrs = mkAddrs 0 $ M.keys locMap
    (sidArgMap, ps) <- foldM (go pubkeys) (M.empty, []) $ M.assocs locMap
    return (sidArgMap, addrs <> line <> vsep ps)
    where
        go pubKeys (m, ps) (lname, ldata) = do
            (mainName, nSidArgs, p) <- extractLoc pubKeys (lname, ldata)
            return (M.insert lname (mainName, nSidArgs) m, ps ++ [p])
        mkAddrs :: Int -> [LocalityName] -> OwlDoc
        mkAddrs n [] = owlpretty ""
        mkAddrs n (l:locs) =
            owlpretty "pub const" <+> owlpretty l <> owlpretty "_addr: &str =" <+> dquotes (owlpretty "127.0.0.1:" <> owlpretty (9001 + n)) <> owlpretty ";" <> line <>
            mkAddrs (n+1) locs

entryPoint :: M.Map LocalityName LocalityData -> [(NameData, [(LocalityName, Int)])] -> [NameData] -> M.Map LocalityName (String, Int) -> ExtractionMonad (OwlDoc)
entryPoint locMap sharedNames pubKeys sidArgMap = do
    let allLocs = M.keys locMap
    sharedNameInits <- mapM genSharedNameInit sharedNames
    let salt = genSalt
    let writeConfigs = map (writeConfig (map (\(p,_,_,_) -> p) pubKeys)) $ M.assocs locMap
    let idxLocCounts = map genIdxLocCount $ M.assocs locMap
    let config = owlpretty "if" <+> (hsep . punctuate (owlpretty " && ") . map owlpretty $ ["args.len() >= 3", "args[1] == \"config\""]) <>
            (braces . vsep $ [vsep idxLocCounts, vsep sharedNameInits, salt, vsep writeConfigs]) <> owlpretty "else"
    allLocsSidArgs <- mapM (\l -> do
                                    let nSidArgs = sidArgMap M.!? l
                                    case nSidArgs of
                                        Just (m, n) -> return (l, m, n)
                                        Nothing -> throwError $ ErrSomethingFailed $ "couldn't look up number of sessionID args for " ++ l ++ ", bug in extraction"
                            ) allLocs
    let runLocs = map genRunLoc allLocsSidArgs
    return $ owlpretty "fn main()" <+> lbrace <> line <>
        owlpretty "let args: Vec<String> = env::args().collect();" <> line <>
        vsep runLocs <> line <>
        config <>
        braces (owlpretty "println!(\"Incorrect usage\");") <> line <>
        rbrace
    where
        genIdxLocCount (lname, (npids,_,_,_,_)) =
            if npids == 0 then owlpretty "" else
                owlpretty "let n_" <> owlpretty (locName lname) <+> owlpretty "= get_num_from_cmdline" <> (parens . dquotes $ owlpretty lname) <> owlpretty ";"

        genSharedNameInit ((name, nt, nsids, _), locs) = do
            let rName = rustifyName name
            let nTotalPids = sum . map snd $ locs
            if nTotalPids == 0 then
                nameInit name nt
            else if nTotalPids == 1 then do
                idxLocName <- case find (\(_,n) -> n == 1) locs of
                                Just (l,_) -> return l
                                Nothing -> throwError $ ErrSomethingFailed "should be unreachable"
                ni <- nameInit "tmp" nt
                return $ owlpretty "let mut" <+> owlpretty (rustifyName name) <+> owlpretty "= HashMap::new();" <> line <>
                    owlpretty "for i in 0..n_" <> owlpretty (locName idxLocName) <> braces (ni <+> owlpretty (rustifyName name) <> owlpretty ".insert(i, owl_tmp);")
            else throwError $ UnsupportedSharedIndices "can't have a name shared by multiple PID-parameterized localities"

        genSalt = owlpretty "let" <+> owlpretty "salt" <+> owlpretty "=" <+> owlpretty "owl_util::gen_rand_bytes(64);" -- use 64 byte salt 

        writeConfig pubKeys (loc, (npids, _, ss, _, _)) =
            let configInits = hsep . punctuate comma $
                    (map (\(n,_,_,_) -> owlpretty (rustifyName n) <+> owlpretty ":" <+> owlpretty (rustifyName n) <> (if npids == 0 then owlpretty "" else owlpretty ".get(&i).unwrap()") <> owlpretty ".clone()") ss ++
                     map (\n -> owlpretty "pk_" <> owlpretty (rustifyName n) <+> owlpretty ":" <+> owlpretty "pk_" <> owlpretty (rustifyName n) <> owlpretty ".clone()") pubKeys ++
                     [owlpretty "salt" <+> owlpretty ":" <+> owlpretty "salt" <> owlpretty ".clone()"]) in
            (if npids == 0 then owlpretty "" else owlpretty "for i in 0..n_" <> owlpretty (locName loc) <+> lbrace) <>
            owlpretty "let" <+> owlpretty (locName loc) <> owlpretty "_config" <+> owlpretty "=" <+> owlpretty (locName loc) <> owlpretty "_config" <+> braces configInits <> owlpretty ";" <> line <>
            owlpretty "let" <+> owlpretty (locName loc) <> owlpretty "_config_serialized" <+> owlpretty "=" <+>
                    owlpretty "serde_json::to_string" <> parens (owlpretty "&" <> owlpretty (locName loc) <> owlpretty "_config") <> owlpretty ".unwrap();" <> line <>
            owlpretty "let mut" <+> owlpretty (locName loc) <> owlpretty "_f" <+> owlpretty "=" <+>
                owlpretty "fs::File::create(format!(\"{}/{}" <> (if npids == 0 then owlpretty "" else owlpretty "_{}") <> owlpretty ".owl_config\", &args[2]," <+>
                    dquotes (owlpretty (locName loc)) <> (if npids == 0 then owlpretty "" else owlpretty ",i") <> owlpretty ")).expect(\"Can't create config file\");" <> line <>
            owlpretty (locName loc) <> owlpretty "_f" <> owlpretty ".write_all" <> parens (owlpretty (locName loc) <> owlpretty "_config_serialized.as_bytes()")
                                <> owlpretty ".expect(\"Can't write config file\");" <>
            (if npids == 0 then owlpretty "" else rbrace)

        genRunLoc (loc, mainName, nSidArgs) =
            let body = genRunLocBody loc mainName nSidArgs in
            owlpretty "if" <+> (hsep . punctuate (owlpretty " && ") . map owlpretty $ ["args.len() >= 4", "args[1] == \"run\"", "args[2] == \"" ++ loc ++ "\""]) <>
                braces body <> owlpretty "else"
        genRunLocBody loc mainName nSidArgs =
            owlpretty "let mut s =" <+> owlpretty (locName loc) <> owlpretty "::init_" <> owlpretty (locName loc) <>
                parens (owlpretty "&args[3]") <> owlpretty ";" <> line <>
            owlpretty "println!(\"Waiting for 5 seconds to let other parties start...\");" <> line <>
            owlpretty "thread::sleep(Duration::new(5, 0));" <> line <>
            owlpretty "println!(\"Running" <+> owlpretty mainName <+> owlpretty "...\");" <> line <>
            owlpretty "let now = Instant::now();" <> line <>
            owlpretty "let res = s." <> owlpretty mainName <> tupled [owlpretty i | i <- [1..nSidArgs]] <> owlpretty ";" <> line <>
            owlpretty "let elapsed = now.elapsed();" <> line <>
            owlpretty "println!" <> parens (dquotes (owlpretty loc <+> owlpretty "returned {:?}") <> owlpretty "," <+> owlpretty "res") <> owlpretty ";" <> line <>
            owlpretty "println!" <> parens (dquotes (owlpretty "Elapsed: {:?}") <> owlpretty "," <+> owlpretty "elapsed") <> owlpretty ";"


-------------------------------------------------------------------------------------------
-- Decl extraction


extractTyDefs :: [(TyVar, TB.TyDef)] -> ExtractionMonad (OwlDoc)
extractTyDefs [] = return $ owlpretty ""
extractTyDefs ((tv, td):ds) = do
    dExtracted <- extractTyDef tv td
    dsExtracted <- extractTyDefs ds
    return $ dExtracted <> line <> line <> dsExtracted
    where
        extractTyDef name (TB.EnumDef cases) = do
            let (_, cases') = unsafeUnbind cases
            extractEnum name cases'
        extractTyDef name (TB.StructDef fields) = do
            let (_, fields') = unsafeUnbind fields
            extractStruct name fields'
        extractTyDef name (TB.TyAbbrev t) = do
            lct <- layoutCTy . doConcretifyTy $ t
            typeLayouts %= M.insert (rustifyName name) lct
            return $ owlpretty ""
        extractTyDef name TB.TyAbstract = do
            typeLayouts %= M.insert (rustifyName name) (LBytes 0) -- Replaced later when instantiated
            return $ owlpretty ""

preamble :: ExtractionMonad (OwlDoc)        
preamble = do
    c <- showAEADCipher
    h <- showHMACMode
    return $ vsep $ map owlpretty
        [   "#![allow(non_camel_case_types)]",
            "#![allow(non_snake_case)]",
            "#![allow(non_upper_case_globals)]",
            "pub use std::rc::Rc;",
            "pub use std::io::{self, Write, BufRead};",
            "pub use std::net::{TcpListener, TcpStream, ToSocketAddrs, SocketAddr};",
            "pub use std::thread;",
            "pub use std::str;",
            "pub use std::fs;",
            "pub use std::time::Duration;",
            "pub use serde::{Serialize, Deserialize};",
            "pub use std::env;",
            "pub use std::collections::HashMap;",
            "pub use std::time::Instant;",
            "pub use owl_crypto_primitives::owl_aead;",
            "pub use owl_crypto_primitives::owl_hmac;",
            "pub use owl_crypto_primitives::owl_pke;",
            "pub use owl_crypto_primitives::owl_util;",
            "pub use owl_crypto_primitives::owl_dhke;",
            "pub use owl_crypto_primitives::owl_hkdf;",
            "const CIPHER: owl_aead::Mode = " ++ c ++ ";",
            "const KEY_SIZE: usize = owl_aead::key_size(CIPHER);",
            "const TAG_SIZE: usize = owl_aead::tag_size(CIPHER);",
            "const NONCE_SIZE: usize = owl_aead::nonce_size(CIPHER);",
            "const HMAC_MODE: owl_hmac::Mode = " ++ h ++ ";"
        ] ++
        [   owlOpsTraitDef,
            owlOpsTraitImpls,
            owl_msgDef,
            owl_outputDef,
            owl_inputDef,
            owl_miscFns,
            owlpretty ""
        ]
    where
        owlOpsTraitDef = vsep $ map owlpretty [
                "trait OwlOps {",
                    "fn owl_output<A: ToSocketAddrs>(&self, dest_addr: &A, ret_addr: &str) -> ();",
                    "fn owl_enc(&self, key: &[u8]) -> Vec<u8>;",
                    "fn owl_dec(&self, key: &[u8]) -> Option<Vec<u8>>;",
                    "fn owl_eq(&self, other: &Self) -> bool",
                        "where Self: PartialEq",
                    "{",
                        "self == other",
                    "}",
                    "fn owl_length(&self) -> usize;",
                    "fn owl_mac(&self, key: &[u8]) -> Vec<u8>;",
                    "fn owl_mac_vrfy(&self, key: &[u8], value: &[u8]) -> Option<Vec<u8>>;",
                    "fn owl_pkenc(&self, pubkey: &[u8]) -> Vec<u8>;",
                    "fn owl_pkdec(&self, privkey: &[u8]) -> Vec<u8>;",
                    "fn owl_sign(&self, privkey: &[u8]) -> Vec<u8>;",
                    "fn owl_vrfy(&self, pubkey: &[u8], signature: &[u8]) -> Option<Vec<u8>>;",
                    "fn owl_dh_combine(&self, others_pk: &[u8]) -> Vec<u8>;",
                    "fn owl_dhpk(&self) -> Vec<u8>;",
                    "fn owl_extract_expand_to_len(&self, salt: &[u8], len: usize) -> Vec<u8>;",
                    "fn owl_xor(&self, other: &[u8]) -> Vec<u8>;",
                "}"
            ]
        owlOpsTraitImpls = vsep $ map owlpretty [
                "impl OwlOps for &[u8] {",
                    "fn owl_output<A: ToSocketAddrs>(&self, dest_addr: &A, ret_addr: &str) -> () {",
                        "output(self, dest_addr, ret_addr);",
                    "}",
                    "fn owl_enc(&self, key: &[u8]) -> Vec<u8> {",
                        "match owl_aead::encrypt_combined(CIPHER, &key[..KEY_SIZE], self, &key[KEY_SIZE..], &[]) {",
                            "Ok(c) => c,",
                            "Err(e) => {",
                                "dbg!(e);",
                                "vec![]",
                            "}",
                        "}",
                    "}",
                    "fn owl_dec(&self, key: &[u8]) -> Option<Vec<u8>> {",
                        "match owl_aead::decrypt_combined(CIPHER, &key[..KEY_SIZE], self, &key[KEY_SIZE..], &[]) {",
                            "Ok(p) => Some(p),",
                            "Err(e) => {",
                                "dbg!(e);",
                                "None",
                            "}",
                        "}",
                    "}",
                    "fn owl_length(&self) -> usize {",
                        "self.len()",
                    "}",
                    "fn owl_mac(&self, key: &[u8]) -> Vec<u8> {",
                        "owl_hmac::hmac(HMAC_MODE, &key[..], self, None)",
                    "}",
                    "fn owl_mac_vrfy(&self, key: &[u8], value: &[u8]) -> Option<Vec<u8>> {",
                        "if owl_hmac::verify(HMAC_MODE, &key[..], self, &value[..], None) {",
                            "Some(self.to_vec())",
                        "} else {",
                            "None",
                        "}",
                    "}",
                    "fn owl_pkenc(&self, pubkey: &[u8]) -> Vec<u8> {",
                        "owl_pke::encrypt(&pubkey[..], self)",
                    "}",
                    "fn owl_pkdec(&self, privkey: &[u8]) -> Vec<u8> {",
                        "owl_pke::decrypt(&privkey[..], self)",
                    "}",
                    "fn owl_sign(&self, privkey: &[u8]) -> Vec<u8> {",
                        "owl_pke::sign(&privkey[..], self)",
                    "}",
                    "fn owl_vrfy(&self, pubkey: &[u8], signature: &[u8]) -> Option<Vec<u8>> {",
                        "if owl_pke::verify(&pubkey[..], &signature[..], self) {",
                            "Some(self.to_vec())",
                        "} else {",
                            "None",
                        "}",
                    "}",
                    "fn owl_dh_combine(&self, others_pk: &[u8]) -> Vec<u8> {",
                        "owl_dhke::ecdh_combine(self, &others_pk[..])",
                    "}",
                    "fn owl_dhpk(&self) -> Vec<u8> {",
                        "owl_dhke::ecdh_dhpk(self)",
                    "}",
                    "fn owl_extract_expand_to_len(&self, salt: &[u8], len: usize) -> Vec<u8> {",
                        "owl_hkdf::extract_expand_to_len(self, salt, len)",
                    "}",
                    "fn owl_xor(&self, other: &[u8]) -> Vec<u8> {",
                        "{let c: Vec<u8> = self.iter().zip(other).map(|(x, y)| x ^ y).collect(); c}",
                    "}",
                "}",
                "impl OwlOps for Vec<u8> {",
                    "fn owl_output<A: ToSocketAddrs>(&self, dest_addr: &A, ret_addr: &str) -> () { (&self[..]).owl_output(dest_addr, ret_addr) }",
                    "fn owl_enc(&self, key: &[u8]) -> Vec<u8> { (&self[..]).owl_enc(key) }",
                    "fn owl_dec(&self, key: &[u8]) -> Option<Vec<u8>> { (&self[..]).owl_dec(key) }",
                    "fn owl_eq(&self, other: &Self) -> bool { self == other }",
                    "fn owl_length(&self) -> usize { self.len() }",
                    "fn owl_mac(&self, key: &[u8]) -> Vec<u8> { (&self[..]).owl_mac(key) }",
                    "fn owl_mac_vrfy(&self, key: &[u8], value: &[u8]) -> Option<Vec<u8>> { (&self[..]).owl_mac_vrfy(key, value) }",
                    "fn owl_pkenc(&self, pubkey: &[u8]) -> Vec<u8> { (&self[..]).owl_pkenc(pubkey) }",
                    "fn owl_pkdec(&self, privkey: &[u8]) -> Vec<u8> { (&self[..]).owl_pkdec(privkey) }",
                    "fn owl_sign(&self, privkey: &[u8]) -> Vec<u8> { (&self[..]).owl_sign(privkey) }",
                    "fn owl_vrfy(&self, pubkey: &[u8], signature: &[u8]) -> Option<Vec<u8>> { (&self[..]).owl_vrfy(pubkey, signature) } ",
                    "fn owl_dh_combine(&self, others_pk: &[u8]) -> Vec<u8> { (&self[..]).owl_dh_combine(others_pk) }",
                    "fn owl_dhpk(&self) -> Vec<u8> { (&self[..]).owl_dhpk() }",
                    "fn owl_extract_expand_to_len(&self, salt: &[u8], len: usize) -> Vec<u8> { (&self[..]).owl_extract_expand_to_len(salt, len) }",
                    "fn owl_xor(&self, other: &[u8]) -> Vec<u8> { (&self[..]).owl_xor(&other[..]) }",
                "}"
            ]
        owl_msgDef = vsep $ map owlpretty [
                "#[derive(Serialize, Deserialize, Debug)]",
                "pub struct msg {",
                    "ret_addr: String,",
                    "payload: Vec<u8>",
                "}"
            ]
        owl_outputDef = vsep $ map owlpretty [
                "pub fn output<A: ToSocketAddrs>(x: &[u8], dest_addr: &A, ret_addr: &str) {",
                    "let msg = msg { ret_addr: String::from(ret_addr), payload: Vec::from(x) };",
                    "let serialized = serde_json::to_vec(&msg).unwrap();",
                    "let mut stream = TcpStream::connect(dest_addr).unwrap();",
                    "stream.write_all(&serialized).unwrap();",
                    "stream.flush().unwrap();",
                "}"
            ]
        owl_inputDef = vsep $ map owlpretty [
                "pub fn owl_input(listener: &TcpListener) -> (Vec<u8>, String) {",
                    "let (mut stream, _addr) = listener.accept().unwrap();",
                    "let mut reader = io::BufReader::new(&mut stream);",
                    "let received: Vec<u8> = reader.fill_buf().unwrap().to_vec();",
                    "reader.consume(received.len());",
                    "let msg : msg = serde_json::from_slice(&received).expect(\"Couldn't parse input\");",
                    "(msg.payload, msg.ret_addr)",
                "}"
            ]
        owl_miscFns = vsep $ map owlpretty [
                "pub fn get_num_from_cmdline(loc_prompt: &str) -> usize {",
                    "let mut input_text = String::new();",
                    "println!(\"Enter number of {loc_prompt} to generate: \");",
                    "io::stdin()",
                        ".read_line(&mut input_text)",
                        ".expect(\"failed to read from stdin\");",
                    "let n = input_text.trim().parse::<usize>().expect(\"not an int\");",
                    "n",
                "}"
            ]




extractModBody :: TB.ModBody -> ExtractionMonad (OwlDoc) 
extractModBody mb = do
    (locMap, sharedNames, pubKeys) <- preprocessModBody mb
    -- We get the list of tyDefs in reverse order of declaration, so reverse again
    tyDefsExtracted <- extractTyDefs $ reverse (mb ^. TB.tyDefs)
    (sidArgMap, locsExtracted) <- extractLocs pubKeys locMap
    p <- preamble
    ep <- entryPoint locMap sharedNames pubKeys sidArgMap
    return $ p <> line <> tyDefsExtracted <> line <> locsExtracted <> line <> ep

extract :: TB.Env -> String -> TB.ModBody -> IO (Either ExtractionError (OwlDoc))
extract tcEnv path modbody = runExtractionMonad tcEnv (initEnv path (modbody ^. TB.userFuncs)) $ extractModBody modbody
