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
import Debug.Trace
import System.IO
import qualified Text.Parsec as P
import qualified Parse as OwlP
import System.FilePath (takeFileName, (</>))

newtype ExtractionMonad a = ExtractionMonad (StateT Env (ExceptT ExtractionError IO) a)
    deriving (Functor, Applicative, Monad, MonadState Env, MonadError ExtractionError, MonadIO)

runExtractionMonad :: Env -> ExtractionMonad a -> IO (Either ExtractionError a)
runExtractionMonad env (ExtractionMonad m) = runExceptT . evalStateT m $ env

-- Number can be any integer type, ADT means one of our struct/enum representations, VecU8 also includes &[u8], [u8; const len], etc
data RustTy = VecU8 | RcVecU8 | Bool | Number | String | Unit | ADT String | Option RustTy
    deriving (Show, Eq, Generic, Typeable)

instance Pretty RustTy where
  pretty VecU8 = pretty "Vec<u8>"
  pretty RcVecU8 = pretty "Rc<Vec<u8>>"
  pretty Bool = pretty "bool"
  pretty Number = pretty "usize"
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
        pretty "Type error during extraction (this probably means a bug in Owl typechecking):" <+> pretty s
    pretty (UndefinedSymbol s) =
        pretty "Undefined symbol: " <+> pretty s
    pretty OutputWithUnknownDestination =
        pretty "Found a call to `output` without a destination specified. For extraction, all outputs must have a destination locality specified."
    pretty (LocalityWithNoMain s) =
        pretty "Locality" <+> pretty s <+> pretty "does not have a defined main function. For extraction, there should be a defined entry point function: def" <+> pretty s <> pretty "_main () @" <+> pretty s
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
printErr e = print $ pretty e

debugPrint :: Show s => s -> ExtractionMonad ()
debugPrint = liftIO . hPrint stderr

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
printOwlArg (ADT _, s) = "(*" ++ s ++ ".data).as_slice()"
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
        ("enc", (VecU8, \args -> case args of
                -- [(RcVecU8,k), (_,x)] -> return $ x ++ ".owl_enc(&(*" ++ k ++ ").as_slice())"
                -- [(VecU8,k), (_,x)] -> return $ x ++ ".owl_enc(&" ++ k ++ ".as_slice())"
                -- [(_,k), (_,x)] -> return $ x ++ ".owl_enc(&" ++ k ++ ")"
                [k,x,iv] -> return $ printOwlOp "owl_enc" [k,x,iv]
                _ -> throwError $ TypeError $ "got wrong number of args for enc"
        )),
        ("dec", (Option VecU8, \args -> case args of
                -- [(RcVecU8,k), (_,x)] -> return $ x ++ ".owl_dec(&(*" ++ k ++ ").as_slice())"
                -- [(VecU8,k), (_,x)] -> return $ x ++ ".owl_dec(&" ++ k ++ ".as_slice())"
                -- [(_,k), (_,x)] -> return $ x ++ ".owl_dec(&" ++ k ++ ")"
                [k,x] -> return $ printOwlOp "owl_dec" [x,k]
                _ -> throwError $ TypeError $ "got wrong number of args for dec"
        )),
        ("mac", (VecU8, \args -> case args of
                [(_,k), (_,x)] -> return $ x ++ ".owl_mac(&" ++ k ++ ")"
                _ -> throwError $ TypeError $ "got wrong number of args for mac"
        )),
        ("mac_vrfy", (Option VecU8, \args -> case args of
                [(_,k), (_,x), (_,v)] -> return $ x ++ ".owl_mac_vrfy(&" ++ k ++ ", &" ++ v ++ ")"
                _ -> throwError $ TypeError $ "got wrong number of args for dec"
        )),
        ("pkenc", (VecU8, \args -> case args of
                [(_,k), (_,x)] -> return $ x ++ ".owl_pkenc(&" ++ k ++ ")"
                _ -> throwError $ TypeError $ "got wrong number of args for pkenc"
        )),
        ("pkdec", (VecU8, \args -> case args of
                [(_,k), (_,x)] -> return $ x ++ ".owl_pkdec(&" ++ k ++ ")"
                _ -> throwError $ TypeError $ "got wrong number of args for pkdec"
        )),
        ("sign", (VecU8, \args -> case args of
                [(_,k), (_,x)] -> return $ x ++ ".owl_sign(&" ++ k ++ ")"
                _ -> throwError $ TypeError $ "got wrong number of args for sign"
        )),
        ("vrfy", (Option VecU8, \args -> case args of
                [(_,k), (_,x), (_,v)] -> return $ x ++ ".owl_vrfy(&" ++ k ++ ", &" ++ v ++ ")"
                _ -> throwError $ TypeError $ "got wrong number of args for vrfy"
        )),
        -- ("dhpk", (VecU8, \args -> case args of
        --         [(_,x)] -> return $ "pk_" ++ x
        --         _ -> throwError $ TypeError $ "got wrong number of args for dhpk"
        -- )),
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
            [(_,x), (ADT _,y)] -> return $ x ++ ".owl_xor(&" ++ y ++ ".data[..])"
            [(_,x), (_,y)] -> return $ x ++ ".owl_xor(&" ++ y ++ ")"
            _ -> throwError $ TypeError $ "got wrong args for xor"
        )),
        ("andb", (Bool, \args -> case args of
            [(_,x), (_,y)] -> return $ x ++ " && " ++ y
            _ -> throwError $ TypeError $ "got wrong args for andb"
        ))
    ]

initEnv :: String -> Env
initEnv path = Env path defaultCipher defaultHMACMode initFuncs M.empty initTypeLayouts initLenConsts M.empty M.empty S.empty 0

lookupTyLayout :: String -> ExtractionMonad Layout
lookupTyLayout n = do
    ls <- use typeLayouts
    case ls M.!? n of
        Just l -> return l
        Nothing -> do
            debugPrint $ "failed lookupTyLayout: " ++ n ++ " in " ++ show ls
            throwError $ UndefinedSymbol n


flattenNameExp :: NameExp -> String
flattenNameExp n = case n ^. val of
  BaseName _ s -> rustifyName s

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
            AEApp "cipherlen" _ [inner] -> do
                tagSz <- useAeadTagSize
                li <- helper inner
                case li of
                    (LBytes ni) -> return $ LBytes (ni + tagSz)
                    _ -> throwError $ CantLayoutType (CTDataWithLength aexp)
            AEApp "plus" _ [a, b] -> do
                la <- helper a
                lb <- helper b
                case (la, lb) of
                    (LBytes na, LBytes nb) -> return $ LBytes (na + nb)
                    _ -> throwError $ CantLayoutType (CTDataWithLength aexp)
            AEApp "mult" _ [a, b] -> do
                la <- helper a
                lb <- helper b
                case (la, lb) of
                    (LBytes na, LBytes nb) -> return $ LBytes (na * nb)
                    _ -> throwError $ CantLayoutType (CTDataWithLength aexp)
            AEApp "zero" _ _ -> return $ LBytes 0
            AEApp fn _ [] -> do
                lookupTyLayout . rustifyName $ fn -- func name used as a length constant
            _ -> throwError $ CantLayoutType (CTDataWithLength aexp)
    in
    helper aexp
layoutCTy (CTOption ct) = do
    lct <- layoutCTy ct
    return $ LEnum "builtin_option" $ M.fromList [("Some", (1, Just $ lct)), ("None", (2, Just $ LBytes 0))]
layoutCTy (CTVar s) = do
    lookupTyLayout . rustifyName $ s
layoutCTy CTBool = return $ LBytes 1 -- bools are one byte 0 or 1
layoutCTy CTUnit = return $ LBytes 1
layoutCTy (CTName n) = do
    lookupTyLayout . flattenNameExp $ n
layoutCTy (CTVK n) = do
    lookupTyLayout . flattenNameExp $ n
layoutCTy (CTDH_PK n) = do
    lookupTyLayout . flattenNameExp $ n
layoutCTy (CTEnc_PK n) = do
    lookupTyLayout . flattenNameExp $ n
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

genOwlOpsImpl :: String -> Doc ann
genOwlOpsImpl name = pretty ""
    -- "impl OwlOps for" <+> pretty name <+> (braces . vsep $ map pretty [
    --     "fn owl_output<A>(&self, t: &mut Tracked<ITreeToken<A,Endpoint>>, dest_addr: &StrSlice, ret_addr: &StrSlice) { (&(*self.data).as_slice()).owl_output(t, dest_addr, ret_addr) }",
    --     "fn owl_enc(&self, key: &[u8], iv: &[u8]) -> Vec<u8> { (&(*self.data).as_slice()).owl_enc(key, iv) }",
    --     "fn owl_dec(&self, key: &[u8]) -> Option<Vec<u8>> { (&(*self.data).as_slice()).owl_dec(key) }",
    --     -- "fn owl_eq(&self, other: &Self) -> bool { (*self.data).as_slice().owl_eq(&(*other.data).as_slice()) }",
    --     "fn owl_length(&self) -> usize { (*self.data).len() }",
    --     "fn owl_mac(&self, key: &[u8]) -> Vec<u8> { (&(*self.data).as_slice()).owl_mac(key) }",
    --     "fn owl_mac_vrfy(&self, key: &[u8], value: &[u8]) -> Option<Vec<u8>> { (&(*self.data).as_slice()).owl_mac_vrfy(key, value) }",
    --     "fn owl_pkenc(&self, pubkey: &[u8]) -> Vec<u8> { (&(*self.data).as_slice()).owl_pkenc(pubkey) }",
    --     "fn owl_pkdec(&self, privkey: &[u8]) -> Vec<u8> { (&(*self.data).as_slice()).owl_pkdec(privkey) }",
    --     "fn owl_sign(&self, privkey: &[u8]) -> Vec<u8> { (&(*self.data).as_slice()).owl_sign(privkey) }",
    --     "fn owl_vrfy(&self, pubkey: &[u8], signature: &[u8]) -> Option<Vec<u8>> { (&(*self.data).as_slice()).owl_vrfy(pubkey, signature) } ",
    --     "fn owl_dh_combine(&self, others_pk: &[u8]) -> Vec<u8> { (&(*self.data).as_slice()).owl_dh_combine(others_pk) }",
    --     "fn owl_extract_expand_to_len(&self, salt: &[u8], len: usize) -> Vec<u8> { (&(*self.data).as_slice()).owl_extract_expand_to_len(salt, len) }",
    --     "fn owl_xor(&self, other: &[u8]) -> Vec<u8> { (&(*self.data).as_slice()).owl_xor(other) }"
    -- ])

specGenParserSerializer :: String -> ExtractionMonad (Doc ann)
specGenParserSerializer name = do
    -- TODO nesting design---Seq or ADT args---depends on parsing lib
    let parser = pretty "#[verifier(external_body)]" <+> pretty "pub open spec fn parse_" <> pretty name <> parens (pretty "x: Seq<u8>") <+>
                    pretty "->" <+> pretty "Option" <> angles (pretty name) <+> braces (line <>
                    (pretty "todo!()") <> line
                )
    let serializer = pretty "#[verifier(external_body)]" <+> pretty "pub open spec fn serialize_" <> pretty name <> parens (pretty "x:" <+> pretty name) <+>
                    pretty "->" <+> pretty "Seq<u8>" <+> braces (line <>
                    (pretty "todo!()") <> line
                )
    return $ vsep [parser, serializer]

specExtractStruct :: String -> [(String, Ty)] -> ExtractionMonad (Doc ann)
specExtractStruct owlName owlFields = do
    let name = specName owlName
    fields <- mapM (\(n, t) -> (rustifySpecTy . doConcretifyTy) t >>= \t' -> return (n, t')) owlFields
    let structDef = pretty "pub struct" <+> pretty name <> braces (line <> (
                        vsep . punctuate comma . map (\(n, t) -> pretty "pub" <+> pretty (specName n) <+> pretty ":" <+> pretty t) $ fields
                    ) <> line)
    parseSerializeDefs <- specGenParserSerializer name
    constructor <- genConstructor owlName fields
    selectors <- mapM (genFieldSelector owlName) fields
    return $ vsep $ [structDef, parseSerializeDefs, constructor] ++ selectors 
    where
        genConstructor owlName fields = do
            let args = parens . hsep . punctuate comma . map (\(n,_) -> pretty "arg_" <> pretty n <> pretty ": Option<Seq<u8>>") $ fields
            let foldOptAnd (n,_) acc = pretty "option_and!" <> parens (pretty "arg_" <> pretty n <> pretty "," <+> acc)
            let structBody = pretty "Some" <> parens (pretty "serialize_" <> pretty (specName owlName) <>
                    parens (pretty (specName owlName) <> braces (hsep . punctuate comma . map (\(n,_) -> pretty (specName n) <> pretty ": arg_" <> pretty n) $ fields)))
            return $
                pretty "pub open spec fn" <+> pretty owlName <> args <+> pretty "-> Option<Seq<u8>>" <+> braces (line <>
                    foldr foldOptAnd structBody fields
                <> line)
        genFieldSelector owlName (fieldName, fieldTy) = do
            return $ 
                pretty "pub open spec fn" <+> pretty fieldName <> parens (pretty owlName <> pretty ": Option<Seq<u8>>") <+> pretty "-> Option<Seq<u8>>" <+> braces (line <>
                    pretty "option_and!" <> parens (pretty owlName <> comma <+> braces (line <>
                        pretty "let parsed = parse_" <> pretty (specName owlName) <> parens (pretty owlName) <> pretty ";" <> line <>
                        pretty "option_and!" <> parens (pretty "parsed" <> comma <+> pretty "Some" <> parens (pretty "parsed." <> pretty (specName fieldName)))
                    <> line))
                <> line)

specExtractEnum :: String -> [(String, Maybe Ty)] -> ExtractionMonad (Doc ann)
specExtractEnum owlName owlCases = do
    let name = specName owlName
    cases <- mapM (\(n, topt) -> do
                        t' <- case topt of
                            Just t -> Just <$> (rustifySpecTy . doConcretifyTy) t
                            Nothing -> return Nothing
                        return (n, t')) owlCases
    let enumDef = pretty "#[is_variant]" <> line <> pretty "pub enum" <+> pretty name <> braces (line <> (
                        vsep . punctuate comma . map (\(n, t) -> pretty (specName n) <> parens (pretty t)) $ cases
                    ) <> line)
    parseSerializeDefs <- specGenParserSerializer name
    caseConstructors <- mapM (genCaseConstructor name) cases
    return $ vsep $ [enumDef, parseSerializeDefs] ++ caseConstructors
    where
        genCaseConstructor name (caseName, Just caseTy) = do
            return $
                pretty "pub open spec fn" <+> pretty caseName <> parens (pretty "x: Option<Seq<u8>>") <+> pretty "-> Option<Seq<u8>>" <+> braces (line <>
                    pretty "option_and!" <> parens (pretty "x," <+> pretty "Some" <> parens (
                            pretty "serialize_" <> pretty name <> parens (
                                pretty "crate::" <> pretty name <> pretty "::" <> pretty (specName caseName) <> parens (pretty "x")
                            )
                        )) <> line
                )

        genCaseConstructor name (caseName, Nothing) = do
            return $
                pretty "pub open spec fn" <+> pretty caseName <> pretty "()" <+> pretty "-> Option<Seq<u8>>" <+> braces (line <>
                    pretty "Some" <> parens (
                            pretty "serialize_" <> pretty name <> parens (
                                pretty "crate::" <> pretty name <> pretty "::" <> pretty (specName caseName) <> pretty "()"
                            )
                        ) <> line
                )

extractStruct :: String -> [(String, Ty)] -> ExtractionMonad (Doc ann, Doc ann)
extractStruct owlName owlFields = do
    let name = rustifyName owlName
    -- liftIO $ print name
    let parsingOutcomeName = name ++ "_ParsingOutcome"
    let typeDef = pretty "pub struct" <+> pretty name <+> pretty "{ data: Rc<Vec<u8>>, parsing_outcome: " <+> pretty parsingOutcomeName <> pretty "}"
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
    structSpec <- specExtractStruct owlName owlFields
    return $ (vsep $ [typeDef, parsingOutcomeDef, lenValidFnDef, parseFnDef, constructorDef] ++ selectorDefs ++ [owlOpsImpl], structSpec)
    where
        mkStructFuncs owlName parsingOutcomeName owlFields = return $
            M.fromList $
                -- don't need to check arity
                (owlName, (rustifyName owlName, ADT (rustifyName owlName), \args -> return $ (Nothing, show $
                        pretty "construct_" <> (pretty . rustifyName) owlName <>
                            (parens . hsep . punctuate comma . map (\(t,a) -> pretty "&" <> (case t of
                                ADT _ -> parens (pretty "*" <> pretty a <> pretty ".data") <> pretty ".as_slice()"
                                RcVecU8 -> parens (pretty "*" <> pretty a) <> pretty ".as_slice()"
                                VecU8 -> pretty a <> pretty ".as_slice()"
                                _ -> pretty a))
                            $ args)
                        ))) :
                map (\(owlField, _) -> (owlField, (rustifyName owlName, RcVecU8, \args -> do
                    case args of
                      (ADT _, arg) : _ -> do
                        return $ (Nothing, show $
                            pretty "Rc::new(slice_to_vec(get_" <> (pretty . rustifyName) owlField <> pretty "_" <> (pretty . rustifyName) owlName <> 
                                parens (pretty "&mut" <+> pretty arg) <> pretty "))")
                      (VecU8, arg) : _ -> do
                        return $ (Just (arg, owlName), show $
                            pretty "Rc::new(slice_to_vec(get_" <> (pretty . rustifyName) owlField <> pretty "_" <> (pretty . rustifyName) owlName <>
                                parens (pretty "&" <+> pretty owlName) <> pretty "))")
                      (RcVecU8, arg) : _ -> do
                        return $ (Just (arg, owlName), show $
                            pretty "Rc::new(slice_to_vec(get_" <> (pretty . rustifyName) owlField <> pretty "_" <> (pretty . rustifyName) owlName <>
                                parens (pretty "&" <+> pretty owlName) <> pretty "))")
                      _ -> throwError $ TypeError $ "attempt to get from " ++ owlName ++ " with bad args"
                ))) owlFields

        genStructParsingOutcomeDef parsingOutcomeName layoutFields = return $
            pretty "// #[derive(PartialEq, Eq, Debug)]" <> line <>
            pretty "pub enum" <+> pretty parsingOutcomeName <+>
            vsep [  lbrace,
                    pretty "Success" <> parens (hsep $ punctuate comma $ replicate (length layoutFields + 1) $ pretty "usize") <> comma,
                    pretty "Failure" <> comma,
                    rbrace]

        genLenValidFnDef name layoutFields =
            let fieldCheckers = map fieldChecker layoutFields in
            let startsPrettied = hsep $ punctuate comma (map (\(n,_) -> pretty "start_" <> pretty n) layoutFields ++ [pretty "i"]) in
            return $ pretty "#[verifier(external_body)] pub fn" <+> pretty "len_valid_" <> pretty name <> parens (pretty "arg: &[u8]") <+>
                pretty " -> Option" <> (angles . parens . hsep . punctuate comma $ [pretty "usize" | _ <- [0..(length layoutFields)]]) <+> lbrace <> line <>
            pretty "let mut i = 0;" <> line <>
            vsep fieldCheckers <> line <>
            pretty "Some" <> (parens . parens $ startsPrettied) <> line <>
            rbrace
        fieldChecker (n, l) = case l of
            LBytes nb    ->
                pretty "let start_" <> pretty n <+> pretty "= i;" <> line <>
                pretty "if" <+> pretty "slice_len(arg) - i" <+> pretty "<" <+> pretty nb <+> lbrace <> line <>
                pretty "return None;" <> line <>
                rbrace <> line <>
                pretty "i = i +" <+> pretty nb <> pretty ";"
            LStruct sn sfs ->
                pretty "let start_" <> pretty n <+> pretty "= i;" <> line <>
                pretty "match" <+> pretty "len_valid_" <> pretty sn <> parens (pretty "&arg[i..]") <+> lbrace <> line <>
                pretty "Some" <> (parens . parens . hsep . punctuate comma $ [pretty "_" | _ <- [0..(length sfs - 1)]] ++ [pretty "l"]) <+> pretty "=>" <+> braces (pretty "i = i + l;") <> line <>
                pretty "None => " <> braces (pretty "return None;") <> line <>
                rbrace
            LEnum en _   ->
                pretty "let start_" <> pretty n <+> pretty "= i;" <> line <>
                pretty "match" <+> pretty "len_valid_" <> pretty en <> parens (pretty "&arg[i..]") <+> lbrace <> line <>
                pretty "Some(l) => " <> braces (pretty "i = i + l;") <> line <>
                pretty "None => " <> braces (pretty "return None;") <> line <>
                rbrace

        genParseFnDef name parsingOutcomeName layout layoutFields = return $
            pretty "#[verifier(external_body)] pub fn" <+> pretty "parse_into_" <> pretty name <> parens (pretty "arg: &mut" <+> pretty name) <+> lbrace <> line <>
                pretty "match arg.parsing_outcome" <+> lbrace <> line <> 
                    pretty parsingOutcomeName <> pretty "::Failure =>" <+> lbrace <> line <>
                        pretty "match len_valid_" <> pretty name <> parens (pretty "&(*arg.data).as_slice()") <+> lbrace <> line <>
                        pretty "Some" <> (parens . parens . hsep . punctuate comma $ [pretty "idx_" <> pretty j | j <- [0..(length layoutFields)]]) <+>
                            pretty "=>" <+> braces (
                                pretty "arg.parsing_outcome =" <+> pretty parsingOutcomeName <> pretty "::Success" <>
                                    (parens . hsep . punctuate comma $ [pretty "idx_" <> pretty j | j <- [0..(length layoutFields)]]) <>
                                pretty ";"
                            ) <> line <>
                        pretty "None => " <> braces (
                                pretty "arg.data =" <+> pretty "Rc::new(vec_u8_from_elem(0," <+> pretty (lenLayoutFailure layout) <> pretty "));" <> line <>
                                pretty "arg.parsing_outcome =" <+> pretty parsingOutcomeName <> pretty "::Failure;"
                            ) <> line <>
                        rbrace <> line <>
                    rbrace <> comma <> line <>
                    pretty "_ => {}" <>
                rbrace <> line <>
            rbrace


        genConstructorDef name parsingOutcomeName layout layoutFields = do
            let argsPrettied = hsep $ punctuate comma $ map (\(n,_) -> pretty "arg_" <> pretty n <> pretty ": &[u8]") layoutFields
            let startsPrettied = hsep $ punctuate comma (map (\(n,_) -> pretty "start_" <> pretty n) layoutFields ++ [pretty "i"])
            let checkAndExtenders = map (\(n,l) -> checkAndExtender name (lenLayoutFailure layout) parsingOutcomeName n l) layoutFields
            return $ pretty "#[verifier(external_body)] pub fn" <+> pretty "construct_" <> pretty name <> parens argsPrettied <+> pretty "->" <+> pretty name <+> lbrace <> line <>
                pretty "let mut v = vec_u8_from_elem(0,0);" <> line <>
                pretty "let mut i = 0;" <> line <>
                vsep checkAndExtenders <> line <>
                pretty "let res =" <+> pretty name <+> pretty "{ data: Rc::new(v), parsing_outcome:" <+> pretty parsingOutcomeName <> pretty "::Success" <> parens startsPrettied <> pretty "};" <> line <>
                pretty "res" <> line <>
                rbrace
        checkAndExtender name lenFailure parsingOutcomeName n l =
            let structEnumChecker dn = pretty "len_valid_" <> pretty dn <> parens (pretty "arg_" <> pretty n) <+> pretty " == None" in
            let checker = case l of
                    LBytes i     -> pretty "slice_len" <> parens (pretty "arg_" <> pretty n) <+> pretty "!=" <+> pretty i
                    LStruct sn _ -> structEnumChecker sn
                    LEnum en _   -> structEnumChecker en in
            pretty "let start_" <> pretty n <+> pretty "= i;" <> line <>
            pretty "if" <+> checker <+> lbrace <> line <>
            pretty "return" <+> pretty name <+> braces (pretty "data: Rc::new(vec_u8_from_elem(0," <+> pretty lenFailure <> pretty ")), parsing_outcome:" <+> pretty parsingOutcomeName <> pretty "::Failure") <> pretty ";" <> line <>
            rbrace <> line <>
            pretty "extend_vec_u8" <> parens (pretty "&mut v," <+> pretty "arg_" <> pretty n) <> pretty ";" <> line <>
            pretty "i = i + " <> pretty "slice_len" <> parens (pretty "arg_" <> pretty n) <> pretty ";"

        genSelectorDefs name parsingOutcomeName layoutFields = do
            let (_, layoutOffsets) = mapAccumL (\(o,i) (n,l) -> let nextO = o + lenLayoutFailure l in ((nextO, i + 1), (n,l,o,nextO,i))) (0,0) layoutFields
            return $ map (genSelectorDef name parsingOutcomeName (length layoutFields)) layoutOffsets

        genSelectorDef :: String -> String -> Int -> (String, Layout, Int, Int, Int) -> Doc ann
        genSelectorDef name parsingOutcomeName numFields (fieldName, fieldLayout, failOffset, failNextOffset, structIdx) =
            let success_pattern = pretty parsingOutcomeName <> pretty "::Success" <> (parens . hsep . punctuate comma $ [pretty "idx_" <> pretty j | j <- [0..numFields]]) in
            -- return $
            pretty "#[verifier(external_body)] pub fn" <+> pretty "get_" <> pretty fieldName <> pretty "_" <> pretty name <> parens (pretty "arg: &" <+> pretty name) <+> pretty "->" <+> pretty "&[u8]" <+> lbrace <> line <>
            pretty "// parse_into_" <> pretty name <> parens (pretty "arg") <> pretty ";" <> line <>
            pretty "match arg.parsing_outcome {" <> line <>
            success_pattern <+> pretty "=>" <+>
                pretty "slice_subrange(&(*arg.data).as_slice(), idx_" <> pretty structIdx <> pretty ", idx_" <> pretty (structIdx + 1) <> pretty ")," <> line <>
            pretty parsingOutcomeName <> pretty "::Failure => slice_subrange(&(*arg.data).as_slice()," <+> pretty failOffset <> pretty "," <+> pretty failNextOffset <> pretty ")" <> line <>
            pretty "}" <> line <>
            pretty "}"

extractEnum :: String -> [(String, Maybe Ty)] -> ExtractionMonad (Doc ann, Doc ann)
extractEnum owlName owlCases' = do
    let owlCases = M.fromList owlCases'
    let name = rustifyName owlName
    let parsingOutcomeName = name ++ "_ParsingOutcome"
    let cases = M.mapKeys rustifyName $ M.map (fmap doConcretifyTy) owlCases
    layout <- layoutEnum name cases
    layoutCases <- case layout of
      LEnum _ cs -> return cs
      _ -> throwError $ ErrSomethingFailed "layoutEnum returned a non enum layout :("
    let tagsComment = pretty "//" <+> pretty (M.foldlWithKey (\s name (tag,_) -> s ++ name ++ " -> " ++ show tag ++ ", ") "" layoutCases)
    let typeDef = tagsComment <> line <> pretty "pub struct" <+> pretty name <+> pretty "{ data: Rc<Vec<u8>>, parsing_outcome: " <+> pretty parsingOutcomeName <> pretty "}"
    parsingOutcomeDef <- genEnumParsingOutcomeDef parsingOutcomeName
    lenValidFnDef <- genLenValidFnDef name layoutCases
    parseFnDef <- genParseFnDef name parsingOutcomeName layout
    constructorDefs <- genConstructorDefs name parsingOutcomeName layout layoutCases
    let owlOpsImpl = genOwlOpsImpl name
    enumFuncs <- mkEnumFuncs owlName owlCases
    adtFuncs %= M.union enumFuncs
    typeLayouts %= M.insert name layout
    enums %= M.insert (S.fromList (map fst owlCases')) owlName
    enumSpec <- specExtractEnum owlName owlCases'

    return $ (vsep $ [typeDef, parsingOutcomeDef, lenValidFnDef, parseFnDef] ++ constructorDefs ++ [owlOpsImpl], enumSpec)
    where
        mkEnumFuncs owlName owlCases = return $
            M.fromList $
                map (\(owlCase, _) -> (owlCase, (rustifyName owlName, ADT (rustifyName owlName), \args -> return $ (Nothing, show $
                    pretty "construct_" <> (pretty . rustifyName) owlName <> pretty "_" <> (pretty . rustifyName) owlCase <>
                        (parens . hsep . punctuate comma . map (\(t,a) -> pretty "&" <> (case t of
                                ADT _ -> parens (pretty "*" <> pretty a <> pretty ".data") <> pretty ".as_slice()"
                                RcVecU8 -> parens (pretty "*" <> pretty a) <> pretty ".as_slice()"
                                VecU8 -> pretty a <> pretty ".as_slice()"
                                _ -> pretty a)) $ args)
                )))) $ M.assocs owlCases

        genEnumParsingOutcomeDef parsingOutcomeName = return $
            pretty "// #[derive(PartialEq, Eq, Debug)]" <> line <>
            pretty "pub enum" <+> pretty parsingOutcomeName <+>
            vsep [  lbrace,
                    pretty "Success" <> comma,
                    pretty "Failure" <> comma,
                    rbrace]

        genLenValidFnDef name layoutCases =
            let caseCheckers = map caseChecker $ M.assocs layoutCases in
            return $ pretty "#[verifier(external_body)] pub fn" <+> pretty "len_valid_" <> pretty name <> parens (pretty "arg: &[u8]") <+>
                pretty " -> Option<usize>" <+> lbrace <> line <>
            pretty "if slice_len(arg) < 1 { return None; } else " <> line <>
            vsep (punctuate (pretty " else ") caseCheckers) <> line <>
            pretty "else { return None; }" <> line <>
            rbrace
        caseChecker (t, (n, l)) = case l of
            Just (LBytes nb)    ->
                pretty "if *slice_index_get(arg, 0) ==" <+> pretty n <> pretty "u8" <+> pretty "&&" <+> pretty "slice_len(arg) >=" <+> pretty (1 + nb) <+>
                braces (pretty " return Some(" <+> pretty (1 + nb) <> pretty "); ")
            Just (LStruct sn sfs) ->
                pretty "if *slice_index_get(arg, 0) ==" <+> pretty n <> pretty "u8" <+> braces (
                    pretty "match" <+> pretty "len_valid_" <> pretty sn <> parens (pretty "&arg[1..]") <+> lbrace <> line <>
                    pretty "Some" <> (parens . parens . hsep . punctuate comma $ [pretty "_" | _ <- [0..(length sfs - 1)]] ++ [pretty "l"]) <+>
                        pretty "=>" <+> braces (pretty "return Some(1 + l);") <> line <>
                    pretty "None => " <> braces (pretty "return None;") <> line <>
                    rbrace
                )
            Just (LEnum en _)   ->
                pretty "if *slice_index_get(arg, 0) ==" <+> pretty n <> pretty "u8" <+> braces (
                    pretty "let start_" <> pretty n <+> pretty "= i;" <> line <>
                    pretty "match" <+> pretty "len_valid_" <> pretty en <> parens (pretty "&arg[1..]") <+> lbrace <> line <>
                    pretty "Some(l) => " <> braces (pretty "return Some(1 + l);") <> line <>
                    pretty "None => " <> braces (pretty "return None;") <> line <>
                    rbrace
                )
            Nothing ->
                pretty "if arg[0] ==" <+> pretty n <+> braces ( pretty "return Some(slice_len(arg));" )

        genParseFnDef name parsingOutcomeName layout = return $
            pretty "#[verifier(external_body)] pub fn" <+> pretty "parse_into_" <> pretty name <> parens (pretty "arg: &mut" <+> pretty name) <+> lbrace <> line <>
                pretty "match arg.parsing_outcome" <+> lbrace <> line <> 
                    pretty parsingOutcomeName <> pretty "::Failure =>" <+> lbrace <> line <>
                        pretty "match len_valid_" <> pretty name <> parens (pretty "&(*arg.data).as_slice()") <+> lbrace <> line <>
                            pretty "Some(l)" <+>
                                pretty "=>" <+> braces (pretty "arg.parsing_outcome =" <+> pretty parsingOutcomeName <> pretty "::Success;") <> line <>
                            pretty "None => " <> braces (
                                    pretty "arg.data =" <+> pretty "Rc::new(vec_u8_from_elem(0," <+> pretty (lenLayoutFailure layout) <> pretty "));" <> line <>
                                    pretty "arg.parsing_outcome =" <+> pretty parsingOutcomeName <> pretty "::Failure;"
                                ) <> line <>
                        rbrace <> line <>
                    rbrace <> comma <> line <>
                    pretty "_ => {}" <>
                rbrace <> line <>
            rbrace

        genConstructorDefs name parsingOutcomeName layout layoutCases =
            return $ map (genConstructorDef name parsingOutcomeName) $ M.assocs layoutCases

        genConstructorDef :: String -> String -> (String, (Int, Maybe Layout)) -> Doc ann
        genConstructorDef name parsingOutcomeName (tagName, (tag, Just (LBytes 0))) = -- special case for a case with no payload, where the constructor takes no arg
            pretty "#[verifier(external_body)] pub fn" <+> pretty "construct_" <> pretty name <> pretty "_" <> pretty tagName <> pretty "()" <+> pretty "->" <+> pretty name <+> lbrace <> line <>
                pretty "let mut v = vec_u8_from_elem(" <> pretty tag <> pretty "u8, 1);" <> line <>
                pretty "let res =" <+> pretty name <+> pretty "{ data: Rc::new(v), parsing_outcome: " <+> pretty parsingOutcomeName <> pretty "::Success" <> pretty "};" <> line <>
                pretty "res" <> line <>
            rbrace

        genConstructorDef name parsingOutcomeName (tagName, (tag, tagLayout)) =
            -- Failure case for struct is always a zero tag with no payload
            let failureReturn = pretty "return" <+> pretty name <+> braces (pretty "data: Rc::new(vec_u8_from_elem(0, 1)), parsing_outcome: " <+> pretty parsingOutcomeName <> pretty "::Failure") <> pretty ";" in
            let checkAndExtender = case tagLayout of
                    Just (LBytes nb)    ->
                        pretty "if" <+> pretty "slice_len(arg)" <+> pretty "<" <+> pretty nb <+> braces failureReturn <> line <>
                        pretty "extend_vec_u8" <> parens (pretty "&mut v," <+> pretty "slice_subrange(arg, 0, " <> pretty nb <> pretty ")") <> pretty ";" <> line
                    Just (LStruct sn sfs) ->
                        pretty "match" <+> pretty "len_valid_" <> pretty sn <> parens (pretty "arg") <+> lbrace <> line <>
                        pretty "Some" <> (parens . parens . hsep . punctuate comma $ [pretty "_" | _ <- [0..(length sfs - 1)]] ++ [pretty "l"]) <+>
                            pretty "=>" <+> braces (pretty "extend_vec_u8" <> parens (pretty "&mut v," <+> pretty "slice_subrange(arg, 0, l)") <> pretty ";") <> line <>
                        pretty "None => " <> braces failureReturn <> line <>
                        rbrace
                    Just (LEnum en _)   ->
                        pretty "match" <+> pretty "len_valid_" <> pretty en <> parens (pretty "arg") <+> lbrace <> line <>
                        pretty "Some(l) => " <> braces (pretty "extend_vec_u8" <> parens (pretty "&mut v," <+> pretty "slice_subrange(arg, 0, l)") <> pretty ";") <> line <>
                        pretty "None => " <> braces failureReturn <> line <>
                        rbrace
                    Nothing ->
                        pretty "extend_vec_u8(&mut v, &arg.as_slice());"
                in
            pretty "pub fn" <+> pretty "construct_" <> pretty name <> pretty "_" <> pretty tagName <> parens (pretty "arg: &[u8]") <+> pretty "->" <+> pretty name <+> lbrace <> line <>
                pretty "let mut v = vec_u8_from_elem(" <> pretty tag <> pretty "u8, 1);" <> line <>
                checkAndExtender <> line <>
                pretty "let res =" <+> pretty name <+> pretty "{data: Rc::new(v), parsing_outcome: " <+> pretty parsingOutcomeName <> pretty "::Success" <> pretty "};" <> line <>
                pretty "res" <> line <>
            rbrace

-------------------------------------------------------------------------------------------
-- Code generation

rcClone :: Doc ann
rcClone = pretty "rc_clone"

extractAExpr :: M.Map String RustTy -> AExprX -> ExtractionMonad (RustTy, Doc ann, Doc ann)
extractAExpr binds (AEVar _ owlV) = do
    let v = rustifyName . show $ owlV
    case binds M.!? v of
      Nothing -> do
        debugPrint $ "failed to find " ++ show v ++ " in binds: " ++ show binds
        return (VecU8, pretty "", pretty v)
      Just RcVecU8 -> return (RcVecU8, pretty "", rcClone <> parens (pretty "&" <> pretty v))
      Just rt -> return (rt, pretty "", pretty v)
extractAExpr binds (AEApp owlFn fparams owlArgs) = do
    fs <- use funcs
    argsPretties <- mapM (extractAExpr binds . view val) owlArgs
    let preArgs = foldl (\p (_,s,_) -> p <> s) (pretty "") argsPretties
    let args = map (\(r, _, p) -> (r, show p)) argsPretties
    case fs M.!? owlFn of
        Just (rt, f) -> do
            str <- f args
            return (rt, preArgs, pretty str)
        Nothing -> do
            adtfs <- use adtFuncs
            case adtfs M.!? owlFn of
                Just (adt, rt, f) -> do
                    (argvaropt, str) <- f args
                    let s = case argvaropt of
                            Nothing -> pretty ""
                            Just (arg,var) ->
                                pretty "let mut" <+> pretty var <+> pretty "=" <+> pretty adt <+> braces (pretty "data:" <+> pretty arg <> comma <+> pretty "parsing_outcome:" <+> pretty adt <> pretty "_ParsingOutcome::Failure") <> pretty ";" <> line <>
                                pretty "parse_into_" <> pretty adt <> parens (pretty "&mut" <+> pretty var) <> pretty ";"
                    return (rt, preArgs <> s, pretty str)
                Nothing ->
                    if owlFn == "H" then
                        -- special case for the random oracle function
                        let unspanned = map (view val) owlArgs in
                        case (fparams, unspanned) of
                            ([ParamStr roname], [AEVar owlV _]) -> do
                                orcls <- use oracles
                                case orcls M.!? roname of
                                    Nothing -> throwError $ TypeError "unrecognized random oracle"
                                    Just outLen -> do
                                        return (VecU8, pretty "", (pretty . rustifyName . unignore $ owlV) <>
                                                                pretty ".owl_extract_expand_to_len(&self.salt," <+> pretty outLen <> pretty ")")
                            _ -> throwError $ TypeError $ "incorrect args/params to random oracle function"
                    else do
                        if owlFn == "dhpk" then
                            let unspanned = map (view val) owlArgs in
                            case unspanned of
                                [(AEGet nameExp)] -> return (VecU8, pretty "", pretty "&self.pk_" <> pretty (flattenNameExp nameExp))
                                _ -> throwError $ TypeError "got wrong number of args to dhpk"
                        else
                            throwError $ UndefinedSymbol owlFn
extractAExpr binds (AEString s) = return (VecU8, pretty "", dquotes (pretty s) <> pretty ".as_bytes()")
extractAExpr binds (AEInt n) = return (Number, pretty "", pretty n)
extractAExpr binds (AEGet nameExp) =
    case nameExp ^. val of
        BaseName ([], _) s -> return (RcVecU8, pretty "", rcClone <> parens (pretty "&self." <> pretty (flattenNameExp nameExp)))
        BaseName (sidxs, _) s -> return (RcVecU8, pretty "", pretty "self.get_" <> pretty (rustifyName s) <> tupled (map (pretty . sidName . show . pretty) sidxs))
        _ -> throwError $ UnsupportedNameExp nameExp
extractAExpr binds (AEGetEncPK nameExp) = return (RcVecU8, pretty "", rcClone <> parens (pretty "&self.pk_" <> pretty (flattenNameExp nameExp)))
extractAExpr binds (AEGetVK nameExp) = return (RcVecU8, pretty "", rcClone <> parens (pretty "&self.pk_" <> pretty (flattenNameExp nameExp)))
extractAExpr binds (AEPackIdx idx ae) = extractAExpr binds (ae^.val)
extractAExpr binds (AELenConst s) = do
    lcs <- use lenConsts
    case lcs M.!? (rustifyName s) of
      Nothing -> throwError $ UndefinedSymbol s
      Just n -> return (Number, pretty "", pretty n)

-- Some helper functions:
extractSamp :: DistrName -> ExtractionMonad ((RustTy, String), Doc ann)
extractSamp "enc" = return ((VecU8, "coins"), pretty "let coins = owl_sample(itree, nonce_size());")
extractSamp distr = throwError $ UndefinedSymbol distr

extractExpr :: Locality -> M.Map String RustTy -> CExpr -> ExtractionMonad (M.Map String RustTy, RustTy, Doc ann, Doc ann)
extractExpr loc binds CSkip = return (binds, Unit, pretty "", pretty "()")
extractExpr loc binds (CInput xsk) = do
    let ((x, ev), k) = unsafeUnbind xsk
    let rustX = rustifyName . show $ x
    let rustEv = if show ev == "_" then "_" else rustifyName . show $ ev
    (_, rt', prek, kPrettied) <- extractExpr loc (M.insert rustX RcVecU8 binds) k
    let eWrapped = pretty "Rc::new" <> parens (pretty "temp_" <> pretty rustX)
    let letbinding =
            pretty "let" <+> parens (pretty "temp_" <> pretty rustX <> comma <+> pretty rustEv) <+> pretty "=" <+> pretty "owl_input(itree/*, &self.listener */)" <> pretty ";" <> line <>
            pretty "let" <+> pretty rustX <+> pretty "=" <+> eWrapped <> pretty ";"
    return (binds, rt', pretty "", vsep [letbinding, prek, kPrettied])
extractExpr (Locality myLname myLidxs) binds (COutput ae lopt) = do
    (rty, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    let aePrettied' = pretty $ printOwlArg (rty, show aePrettied)
    l <- case lopt of
        Nothing -> throwError OutputWithUnknownDestination
        Just (EndpointLocality (Locality lname _)) -> return $ pretty "&" <> pretty lname <> pretty "_addr()"
        Just (Endpoint ev) -> return $ pretty "&" <> (pretty . rustifyName . show $ ev) <> pretty ".as_str()"
    return $ (binds, Unit, preAe, pretty "owl_output" <> (parens . hsep . punctuate comma $ [pretty "itree", aePrettied', l, pretty "&" <> pretty myLname <> pretty "_addr()"]))
    --{- pretty "&" <> -} aePrettied' <> pretty ".owl_output" <> parens (pretty "itree," <+> l <> comma <+> pretty "&" <> pretty myLname <> pretty "_addr()") {- <> pretty ";" -})
extractExpr loc binds (CLet e xk) = do
    let (x, k) = unsafeUnbind xk
    let rustX = rustifyName . show $ x
    (_, rt, preE, ePrettied) <- extractExpr loc binds e
    (_, rt', preK, kPrettied) <- extractExpr loc (M.insert rustX (if rt == VecU8 then RcVecU8 else rt) binds) k
    let eWrapped = case rt of
            VecU8 -> pretty "Rc::new" <> parens (pretty "temp_" <> pretty rustX)
            RcVecU8 -> rcClone <> parens (pretty "&temp_" <> pretty rustX)
            _ -> pretty "temp_" <> pretty rustX
    let letbinding = case e of
            CSkip -> pretty ""
            _ -> pretty "let" <+> pretty "temp_" <> pretty rustX <+> pretty "=" <+> ePrettied <> pretty ";" <> line <>
                 pretty "let" <+> pretty rustX <+> pretty "=" <+> eWrapped <> pretty ";"
    return (binds, rt', pretty "", vsep [preE, letbinding, preK, kPrettied])
extractExpr loc binds (CSamp distr owlArgs) = do
    fs <- use funcs
    argsPretties <- mapM (extractAExpr binds . view val) owlArgs
    let preArgs = foldl (\p (_,s,_) -> p <> s) (pretty "") argsPretties
    let args = map (\(r, _, p) -> (r, show p)) argsPretties
    case fs M.!? distr of
      Nothing -> do
        throwError $ UndefinedSymbol distr
      Just (rt, f) -> do
        (coins, sampCoinsPrettied) <- extractSamp distr
        str <- f $ args ++ [coins]
        return (binds, VecU8, preArgs, braces (sampCoinsPrettied <+> pretty str))
extractExpr loc binds (CIf ae eT eF) = do
    (_, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    (_, rt, preeT, eTPrettied) <- extractExpr loc binds eT
    (_, rt', preeF, eFPrettied) <- extractExpr loc binds eF
    return (binds, rt, pretty "", preAe <> line <> pretty "if" <+> aePrettied <+> braces (vsep [preeT, eTPrettied]) <+> pretty "else" <+> braces (vsep [preeF, eFPrettied]))
extractExpr loc binds (CRet ae) = do
    (rt, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    return (binds, rt, preAe, aePrettied)
extractExpr loc binds (CCall owlFn (sids, pids) owlArgs) = do
    fs <- use funcs
    argsPretties <- mapM (extractAExpr binds . view val) owlArgs
    let preArgs = foldl (\p (_,s,_) -> p <> s) (pretty "") argsPretties
    let args = map (\sid -> (Number, sidName . show . pretty $ sid)) sids ++ map (\(r, _, p) -> (r, show p)) argsPretties
    case fs M.!? owlFn of
      Nothing -> do
        throwError $ UndefinedSymbol owlFn
      Just (rt, f) -> do
        str <- f args
        return (binds, rt, preArgs, pretty str)
extractExpr loc binds (CCase ae cases) = do
    (rt, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    case rt of
      Option rt' -> do
        casesPrettiedRts <- forM cases $ \(c, o) ->
                case o of
                    Left e -> do
                        (_, rt'', preE, ePrettied) <- extractExpr loc binds e
                        return (rt'', pretty c <+> pretty "=>" <+> braces (vsep [preE, ePrettied]))
                    Right xk -> do
                        let (x, k) = unsafeUnbind xk
                        let rustX = rustifyName . show $ x
                        (_, rt'', preK, kPrettied) <- extractExpr loc (M.insert rustX (if rt' == VecU8 then RcVecU8 else rt') binds) k
                        let eWrapped = case rt' of
                                VecU8 -> pretty "Rc::new" <> parens (pretty "temp_" <> pretty rustX)
                                RcVecU8 -> rcClone <> parens (pretty "&temp_" <> pretty rustX)
                                _ -> pretty "temp_" <> pretty rustX
                        return (rt'', pretty c <> parens (pretty "temp_" <> pretty rustX) <+> pretty "=>"
                                    <+> braces (pretty "let" <+> pretty rustX <+> pretty "=" <+> eWrapped <> pretty ";" <> line <> preK <> line <> kPrettied))
        branchRt <- case casesPrettiedRts of
          [] -> throwError $ TypeError "case on Option type with no cases"
          (b, _) : _ -> return b
        let casesPrettied = map snd casesPrettiedRts
        return (binds, branchRt, pretty "", preAe <> line <> pretty "match " <+> aePrettied <+> (braces . vsep $ casesPrettied))
      _ -> do -- We are casing on an Owl ADT
        es <- use enums
        enumOwlName <- case es M.!? (S.fromList (map fst cases)) of
          Nothing -> throwError $ UndefinedSymbol $ "can't find an enum whose cases are " ++ (show . map fst $ cases)
          Just s -> return s
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
                        return (rt'', pretty b <+> pretty "=>" <+> braces (vsep [preE, ePrettied]))
                    Right xk -> do
                        b <- tagByteOf c
                        let (x, k) = unsafeUnbind xk
                        let rustX = rustifyName . show $ x
                        (_, rt'', preK, kPrettied) <- extractExpr loc (M.insert rustX RcVecU8 binds) k
                        let eWrapped = pretty "Rc::new(caser_tmp.data[1..].to_vec())"
                        return (rt'', pretty b <+> pretty "=>"
                                    <+> braces (pretty "let" <+> pretty rustX <+> pretty "=" <+> eWrapped <> pretty ";" <> line <> preK <> line <> kPrettied))
        branchRt <- case casesPrettiedRts of
          [] -> throwError $ TypeError "case on enum with no cases"
          (b, _) : _ -> return b
        let defaultCase = case branchRt of
              VecU8 -> pretty "vec_u8_from_elem(0,1)"
              RcVecU8 -> pretty "Rc::new(vec_u8_from_elem(0,1))"
              Bool -> pretty "/* arbitrarily autogenerated */ false"
              Number -> pretty "/* arbitrarily autogenerated */ 0"
              String -> pretty "/* arbitrarily autogenerated */ \"\""
              Unit -> pretty "()"
              ADT s -> pretty "{ let mut tmp = (Rc::new(vec_u8_from_elem(0,0))," <+> pretty s <> pretty "_ParsingOutcome::Failure); parse_into_" <> pretty s <> pretty "(&mut tmp); tmp }"
              Option _ -> pretty "/* arbitrarily autogenerated */ None"
        let casesPrettied = map snd casesPrettiedRts
        return (binds, branchRt, pretty "", preAe <> braces (
                pretty "let mut caser_tmp" <+> pretty "=" <+> parens (aePrettied <> comma <+> pretty (rustifyName enumOwlName) <> pretty "_ParsingOutcome::Failure") <> pretty ";" <> line <>
                pretty "parse_into_" <> pretty (rustifyName enumOwlName)  <> parens (pretty "&mut caser_tmp") <> pretty ";" <> line <>
                pretty "match caser_tmp.data[0]" <+> braces (
                    vsep casesPrettied <> line <>
                    pretty "_ =>" <+> defaultCase <> comma
                ))
            )
extractExpr loc binds (CTLookup tbl ae) = do
    (rt, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    aeWrapped <- case rt of
            RcVecU8 -> return $ pretty "&" <> aePrettied <> pretty ".as_slice()"
            VecU8 -> return $ pretty "&" <> aePrettied
            _ -> throwError $ ErrSomethingFailed "got wrong arg type for lookup"
    let tblName = rustifyName tbl
    return (binds, Option VecU8, preAe, pretty "self." <> pretty tblName <> pretty ".get" <> parens aeWrapped <> pretty ".cloned()")
extractExpr loc binds c = throwError $ ErrSomethingFailed $ "unimplemented case for extractExpr: " ++ (show . pretty $ c)

funcCallPrinter :: String -> [(String, RustTy)] -> [(RustTy, String)] -> ExtractionMonad String
funcCallPrinter name rustArgs callArgs = do
    if length rustArgs == length callArgs then
        return $ show $ pretty "self." <> pretty name <> (parens . hsep . punctuate comma . map (\(rty, arg) -> (if rty == Number then pretty "" else pretty "&") <+> pretty arg) $ callArgs)
    else throwError $ TypeError $ "got wrong args for call to " ++ name

extractArg :: (String, RustTy) -> Doc ann
extractArg (s, rt) =
    pretty s <> pretty ": &" <+> pretty rt

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
rustifyArgTy (CTVar n) = do
    l <- lookupTyLayout . rustifyName $ n
    return $ case l of
        LBytes _ -> VecU8
        LStruct s _ -> ADT s
        LEnum s _ -> ADT s
rustifyArgTy CTBool = return Bool
rustifyArgTy CTUnit = return Unit
rustifyArgTy _ = return VecU8

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


makeFunc :: String -> Locality -> [IdxVar] -> [(DataVar, Embed Ty)] -> Ty  -> ExtractionMonad ()
makeFunc owlName _ sidArgs owlArgs owlRetTy = do
    let name = rustifyName owlName
    rustArgs <- mapM rustifyArg owlArgs
    let rustSidArgs = map rustifySidArg sidArgs
    rtb <- rustifyArgTy $ doConcretifyTy owlRetTy
    funcs %= M.insert owlName (rtb, funcCallPrinter name (rustSidArgs ++ rustArgs))
    return ()


extractDef :: String -> Locality -> [IdxVar] -> [(DataVar, Embed Ty)] -> Ty -> Expr -> ExtractionMonad (Doc ann, Doc ann)
extractDef owlName loc sidArgs owlArgs owlRetTy owlBody = do
    let name = rustifyName owlName
    concreteBody <- ANF.anf owlBody >>= concretify
    -- TODO refactor
    concreteBody' <- concretify owlBody
    rustArgs <- mapM rustifyArg owlArgs
    let rustSidArgs = map rustifySidArg sidArgs
    (_, rtb, preBody, body) <- extractExpr loc (M.fromList rustArgs) concreteBody
    decl <- genFuncDecl name rustSidArgs rustArgs rtb
    defSpec <- genDefSpec loc concreteBody' rustArgs (specTyOf rtb)
    funcs %= M.insert owlName (rtb, funcCallPrinter name (rustSidArgs ++ rustArgs))
    return $ (decl <+> lbrace <> line <> preBody <> line <> body <> line <> rbrace, defSpec)
    where
        specRtPrettied specRt = pretty "<Option<" <> pretty specRt <> pretty ">, Endpoint>"
        genFuncDecl name sidArgs owlArgs rt = do
            let itree = pretty "itree: &mut Tracked<ITreeToken" <> specRtPrettied (specTyOf rt) <> pretty ">"
            let argsPrettied =
                    pretty "&mut self," <+> 
                    itree <> comma <+>
                    (hsep . punctuate comma . map (\(a,_) -> pretty a <+> pretty ": usize") $ sidArgs) <+> (hsep . punctuate comma . map extractArg $ owlArgs)
            let rtPrettied = pretty "->" <+> parens (pretty "res:" <+> pretty rt)
            let viewRes = case rt of
                    Unit -> pretty "Some(())"
                    _ -> pretty "res.view()"
            let defReqEns =
                    pretty "requires old(itree)@@ ===" <+> pretty owlName <> pretty "_spec" <> parens (pretty "*old(self)") <> line <>
                    pretty "ensures  itree@@.results_in" <> parens viewRes <> line 
            return $ pretty "pub fn" <+> pretty name <> parens argsPrettied <+> rtPrettied <> line <> defReqEns
        genDefSpec (Locality lname _) body owlArgs specRt = do
            let argsPrettied = pretty "loc:" <+> pretty (locName lname) <> (hsep . punctuate comma . map extractArg $ owlArgs)
            let rtPrettied = pretty "-> ITree" <> specRtPrettied specRt
            return $ pretty "pub open spec fn" <+> pretty owlName <> pretty "_spec" <> parens argsPrettied <+> rtPrettied <+> lbrace <> line <>
                pretty "owl_spec!" <> parens (line <>
                    pretty body
                <> line) <> line <>
                rbrace


nameInit :: String -> NameType -> ExtractionMonad (Doc ann)
nameInit s nt = case nt^.val of
    NT_Nonce -> return $ pretty "let" <+> pretty (rustifyName s) <+> pretty "=" <+> pretty "owl_aead::gen_rand_nonce(cipher());"
    NT_Enc _ -> return $ pretty "let" <+> pretty (rustifyName s) <+> pretty "=" <+> pretty "owl_aead::gen_rand_key(cipher());"
    NT_MAC _ -> return $ pretty "let" <+> pretty (rustifyName s) <+> pretty "=" <+> pretty "owl_hmac::gen_rand_key(&HMAC_MODE());"
    NT_PKE _ -> return $ pretty "let" <+> (parens . hsep . punctuate comma . map pretty $ [rustifyName s, "pk_" ++ rustifyName s]) <+> pretty "=" <+> pretty "owl_pke::gen_rand_keys();"
    NT_Sig _ -> return $ pretty "let" <+> (parens . hsep . punctuate comma . map pretty $ [rustifyName s, "pk_" ++ rustifyName s]) <+> pretty "=" <+> pretty "owl_pke::gen_rand_keys();"
    NT_DH -> return $ pretty "let" <+> (parens . hsep . punctuate comma . map pretty $ [rustifyName s, "pk_" ++ rustifyName s]) <+> pretty "=" <+> pretty "owl_dhke::gen_ecdh_key_pair();"
    _ -> throwError $ ErrSomethingFailed "unimplemented name initializer"


-------------------------------------------------------------------------------------------
-- Handling localities

type LocalityName = String
type NameData = (String, NameType, Int, Int) -- name, type, number of sessionID indices, number of processID indices
type DefData = (String, Locality, [IdxVar], [(DataVar, Embed Ty)], Ty, Expr) -- func name, locality, sessionID arguments, arguments, return type, body
type LocalityData =  (Int, [NameData], [NameData], [DefData], [(String, Ty)]) -- number of locality indices, local state, shared state, defs, table names and codomains

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
                case P.parse OwlP.parseFile (takeFileName fn') s of
                    Left err -> throwError $ CouldntParseInclude $ "parse error: " ++ show err
                    Right dcls -> do
                        preprocessed <- mapM preprocessIncludes dcls
                        return $ concat preprocessed
        d' -> return $ [d]


sortDecls :: [Decl] -> ExtractionMonad ([Decl], M.Map LocalityName LocalityData, [(NameData, [(LocalityName, Int)])], [NameData])
sortDecls dcls = do
    preprocessed <- mapM preprocessIncludes dcls
    foldM go ([], M.empty, [], []) $ concat preprocessed
    where
    go (gDecls, locMap, shared, pubkeys) d = case d^.val of
        DeclName name binds -> do
            let ((sids, pids), ntnlOpt) = unsafeUnbind binds
            case ntnlOpt of
              Nothing -> return (gDecls, locMap, shared, pubkeys) -- ignore abstract names, they should be concretized when used
              Just (nt, loc) -> do
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
                let locNames = map (\(Locality lname _) -> lname) loc
                let locNameCounts = map (\(Locality lname lidxs) -> (lname, length lidxs)) loc
                case nt ^.val of
                    -- public keys must be shared, so pub/priv key pairs are generated by the initializer
                    NT_PKE _ ->
                        return (gDecls, foldl gPub locMap locNames, shared ++ [((name, nt, nsids, npids), locNameCounts)], pubkeys ++ [(name, nt, nsids, npids)])
                    NT_Sig _ ->
                        return (gDecls, foldl gPub locMap locNames, shared ++ [((name, nt, nsids, npids), locNameCounts)], pubkeys ++ [(name, nt, nsids, npids)])
                    NT_DH ->
                        return (gDecls, foldl gPub locMap locNames, shared ++ [((name, nt, nsids, npids), locNameCounts)], pubkeys ++ [(name, nt, nsids, npids)])
                    _ -> if length loc /= 1 then
                            -- name is shared among multiple localities
                            return (gDecls, foldl gPub locMap locNames, shared ++ [((name, nt, nsids, npids), locNameCounts)], pubkeys)
                        else
                            -- name is local and can be locally generated
                            return (gDecls, foldl gPriv locMap locNames, shared, pubkeys)
        DeclDef name binds -> do
            let ((sids, pids), (Locality loc lidxs, binds')) = unsafeUnbind binds
            let (args, (_, retTy, obody)) = unsafeUnbind binds'
            case obody of
              Just body -> do
                let f (i, l, s, d, t) = (i, l, s, d ++ [(name, Locality loc lidxs, sids, args, retTy, body)], t)
                return (gDecls, M.adjust f loc locMap, shared, pubkeys)
              Nothing -> do -- Def is abstract, predeclare it
                  makeFunc name (Locality loc lidxs) sids args retTy
                  return (gDecls, locMap, shared, pubkeys)
        DeclEnum n c -> return (gDecls ++ [d], locMap, shared, pubkeys)
        DeclStruct n f -> return (gDecls ++ [d], locMap, shared, pubkeys)
        DeclLocality l idxs -> do
            if idxs >= 2 then throwError $ ErrSomethingFailed "we don't support multiple-arity party IDs at the moment"
            else return (gDecls, M.insert l (idxs, [],[],[], []) locMap, shared, pubkeys)
        DeclRandOrcl n _ (arg, rty) -> do
            rtlen <- case rty ^. val of
                NT_Nonce -> return "nonce_size()"
                NT_Enc _ -> return "key_size() + nonce_size()"
                _ -> throwError $ UnsupportedOracleReturnType n
            oracles %= M.insert n rtlen
            return (gDecls, locMap, shared, pubkeys)
        DeclCorr _ _ -> return (gDecls, locMap, shared, pubkeys) -- purely ghost
        DeclDetFunc name _ _ ->
            if name == "xor" then return (gDecls, locMap, shared, pubkeys) -- We do support xor if needed
            else throwError $ UnsupportedDecl "can't use uninterpreted functions in extracted protocols"
        DeclTable name ty (Locality lname _) -> do
            let f (i, l, s, d, t) = (i, l, s, d, t ++ [(name, ty)])
            return (gDecls, M.adjust f lname locMap, shared, pubkeys)
        DeclTy name topt -> do
            return (gDecls ++ [d], locMap, shared, pubkeys)
        DeclInclude fn -> throwError $ ErrSomethingFailed "messed up"


-- return number of arguments to main and the print of the locality
extractLoc :: [NameData] -> (LocalityName, LocalityData) -> ExtractionMonad (Int, Doc ann, Doc ann)
extractLoc pubKeys (loc, (idxs, localNames, sharedNames, defs, tbls)) = do
    let sfs = stateFields idxs localNames sharedNames pubKeys tbls
    let cfs = configFields idxs sharedNames pubKeys
    indexedNameGetters <- mapM genIndexedNameGetter localNames
    let sharedIndexedNameGetters = map genSharedIndexedNameGetter sharedNames
    case find (\(n,_,sids,as,_,_) -> (n == loc ++ "_main") && null as) defs of
        Just (_,_,sids,_,_,_) -> do
            initLoc <- genInitLoc loc localNames sharedNames pubKeys tbls
            (fns, fnspecs) <- unzip <$> mapM (\(n, l, sids, as, t, e) -> extractDef n l sids as t e) defs
            return $ (length sids,
                pretty "// #[derive(Serialize, Deserialize, Debug)]" <> line <> pretty "pub struct" <+> pretty (locName loc) <> pretty "_config" <+> braces cfs <> line <>
                pretty "pub struct" <+> pretty (locName loc) <+> braces sfs <> line <>
                pretty "impl" <+> pretty (locName loc) <+> braces (line <> initLoc <+> vsep (indexedNameGetters ++ sharedIndexedNameGetters ++ fns)),
                vsep fnspecs)
        Nothing -> throwError $ LocalityWithNoMain loc
    where
        genIndexedNameGetter (n, nt, nsids, _) = if nsids == 0 then return $ pretty "" else do
            ni <- nameInit n nt
            return $
                pretty "pub fn get_" <> pretty (rustifyName n) <> tupled (pretty "&mut self" : [pretty "sid" <> pretty n <> pretty ": usize" | n <- [0..(nsids-1)]]) <+> pretty "-> Rc<Vec<u8>>" <> lbrace <> line <>
                    pretty "match self." <> pretty (rustifyName n) <> pretty ".get" <> parens (tupled ([pretty "&sid" <> pretty n | n <- [0..(nsids-1)]])) <> lbrace <> line <>
                        pretty "Some(v) =>" <+> rcClone <> pretty "(v)," <> line <>
                        pretty "None =>" <+> lbrace <> line <>
                            ni <> line <>
                            pretty "let v = Rc::new" <> parens (pretty (rustifyName n)) <> pretty ";" <> line <>
                            pretty "self." <> pretty (rustifyName n) <> pretty ".insert" <> parens (tupled ([pretty "sid" <> pretty n | n <- [0..(nsids-1)]]) <> comma <+> rcClone <> pretty "(&v)") <> pretty ";" <> line <>
                            rcClone <> pretty "(&v)" <> line <>
                        rbrace <>
                    rbrace <>
                rbrace
        genSharedIndexedNameGetter (n, _, nsids, _) = if nsids == 0 then pretty "" else
            pretty "pub fn get_" <> pretty (rustifyName n) <> tupled (pretty "&self" : [pretty "sid" <> pretty n <> pretty ": usize" | n <- [0..(nsids-1)]]) <+> pretty "-> Rc<Vec<u8>>" <> lbrace <> line <>
                rcClone <> parens (pretty "&self." <> pretty (rustifyName n)) <>
            rbrace

        configFields idxs sharedNames pubKeys =
            vsep . punctuate comma $
                map (\(s,_,_,npids) -> pretty (rustifyName s) <> (if npids == 0 || (idxs == 1 && npids == 1) then pretty ": Vec<u8>" else pretty ": HashMap<usize, Vec<u8>>")) sharedNames ++
                map (\(s,_,_,_) -> pretty "pk_" <> pretty (rustifyName s) <> pretty ": Vec<u8>") pubKeys ++
                [pretty "salt" <> pretty ": Vec<u8>"]
        stateFields idxs localNames sharedNames pubKeys tbls =
            vsep . punctuate comma $
                pretty "// pub listener: TcpListener" :
                map (\(s,_,nsids,npids) -> pretty "pub" <+> pretty (rustifyName s) <>
                        if nsids == 0
                        then pretty ": Rc<Vec<u8>>"
                        else pretty ": HashMap" <> angles ((tupled [pretty "usize" | _ <- [0..(nsids - 1)]]) <> comma <+> pretty "Rc<Vec<u8>>")
                    ) localNames ++
                map (\(s,_,_,npids) -> pretty "pub" <+> pretty (rustifyName s) <> (if npids == 0 || (idxs == 1 && npids == 1) then pretty ": Rc<Vec<u8>>" else pretty ": Rc<HashMap<usize, Vec<u8>>>")) sharedNames ++
                map (\(s,_,_,_) -> pretty "pub" <+> pretty "pk_" <> pretty (rustifyName s) <> pretty ": Rc<Vec<u8>>") pubKeys ++
                -- Tables are always treated as local:
                map (\(n,t) -> pretty "pub" <+> pretty (rustifyName n) <> pretty ": HashMap<Vec<u8>, Vec<u8>>") tbls ++
                [pretty "pub" <+> pretty "salt" <> pretty ": Rc<Vec<u8>>"]
        genInitLoc loc localNames sharedNames pubKeys tbls = do
            localInits <- mapM (\(s,n,i,_) -> if i == 0 then nameInit s n else return $ pretty "") localNames
            return $ pretty "#[verifier(external_body)] pub fn init_" <> pretty (locName loc) <+> parens (pretty "config_path : &StrSlice") <+> pretty "-> Self" <+> lbrace <> line <>
                pretty "// let listener = TcpListener::bind" <> parens (pretty loc <> pretty "_addr().into_rust_str()") <> pretty ".unwrap();" <> line <>
                vsep localInits <> line <>
                pretty "let config_str = fs::read_to_string(config_path.into_rust_str()).expect(\"Config file not found\");" <> line <>
                pretty "let config:" <+> pretty (locName loc) <> pretty "_config =" <+> pretty "todo!(); // serde_json::from_str(&config_str).expect(\"Can't parse config file\");" <> line <>
                pretty "return" <+> pretty (locName loc) <+>
                    braces (hsep . punctuate comma $
                        -- pretty "/* listener */"  :
                        map (\(s,_,nsids,_) ->
                                if nsids == 0
                                then (pretty . rustifyName $ s) <+> pretty ":" <+> pretty "Rc::new" <> parens (pretty . rustifyName $ s)
                                else (pretty . rustifyName $ s) <+> pretty ":" <+> pretty "HashMap::new()"
                            ) localNames ++
                        map (\(s,_,_,_) -> pretty (rustifyName s) <+> pretty ":" <+> pretty "Rc::new" <> parens (pretty "config." <> pretty (rustifyName s))) sharedNames ++
                        map (\(s,_,_,_) -> pretty "pk_" <> pretty (rustifyName s) <+> pretty ":" <+> pretty "Rc::new" <> parens (pretty "config." <> pretty "pk_" <> pretty (rustifyName s))) pubKeys ++
                        map (\(n,_) -> pretty (rustifyName n) <+> pretty ":" <+> pretty "HashMap::new()") tbls ++
                        [pretty "salt : Rc::new(config.salt)"]
                    ) <>
                rbrace

extractLocs :: [NameData] ->  M.Map LocalityName LocalityData -> ExtractionMonad (M.Map LocalityName Int, Doc ann, Doc ann)
extractLocs pubkeys locMap = do
    let addrs = mkAddrs 0 $ M.keys locMap
    let specEndpoint = mkSpecEndpoint $ M.keys locMap
    (sidArgMap, ps, spec_ps) <- foldM (go pubkeys) (M.empty, [], []) $ M.assocs locMap
    return (sidArgMap, addrs <> line <> vsep ps, specEndpoint <> line <> endpointOfAddr <> line <> line <> (vsep . punctuate line $ spec_ps))
    where
        go pubKeys (m, ps, spec_ps) (lname, ldata) = do
            (nSidArgs, p, spec_p) <- extractLoc pubKeys (lname, ldata)
            return (M.insert lname nSidArgs m, ps ++ [p], spec_ps ++ [spec_p])
        mkAddrs :: Int -> [LocalityName] -> Doc ann
        mkAddrs n [] = pretty ""
        mkAddrs n (l:locs) =
            pretty "#[verifier(external_body)] pub const fn" <+> pretty l <> pretty "_addr() -> (a:StrSlice<'static>)" <> line <>
                pretty "ensures endpoint_of_addr(a.view()) ==" <+> pretty "Endpoint::Loc_" <> pretty l <> line <> 
            braces (line <> pretty "new_strlit" <> parens (dquotes (pretty "127.0.0.1:" <> pretty (9001 + n))) <> line) <> line <>
            mkAddrs (n+1) locs
        mkSpecEndpoint lnames = 
            pretty "#[is_variant]" <> line <> pretty "#[derive(Copy, Clone)]" <> line <> 
            pretty "pub enum Endpoint" <+> braces (line <> 
                (vsep . punctuate comma . map (\s -> pretty "Loc_" <> pretty s) $ lnames)
            <> line)
        endpointOfAddr = pretty "#[verifier(external_body)] pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint { todo!() }"

entryPoint :: M.Map LocalityName LocalityData -> [(NameData, [(LocalityName, Int)])] -> [NameData] -> M.Map LocalityName Int -> ExtractionMonad (Doc ann)
entryPoint locMap sharedNames pubKeys sidArgMap = do
    let allLocs = M.keys locMap
    sharedNameInits <- mapM genSharedNameInit sharedNames
    let salt = genSalt
    let writeConfigs = map (writeConfig (map (\(p,_,_,_) -> p) pubKeys)) $ M.assocs locMap
    let idxLocCounts = map genIdxLocCount $ M.assocs locMap
    let config = pretty "if" <+> (hsep . punctuate (pretty " && ") . map pretty $ ["args.len() >= 3", "args[1] == \"config\""]) <>
            (braces . vsep $ [vsep idxLocCounts, vsep sharedNameInits, salt, vsep writeConfigs]) <> pretty "else"
    allLocsSidArgs <- mapM (\l -> do
                                    let nSidArgs = sidArgMap M.!? l
                                    case nSidArgs of
                                        Just n -> return (l, n)
                                        Nothing -> throwError $ ErrSomethingFailed $ "couldn't look up number of sessionID args for " ++ l ++ ", bug in extraction"
                            ) allLocs
    let runLocs = map genRunLoc allLocsSidArgs
    return $ pretty "#[verifier(external_body)]" <> line <> pretty "fn main()" <+> lbrace <> line <>
        pretty "let args: std::vec::Vec<std::string::String> = env::args().collect();" <> line <>
        vsep runLocs <> line <>
        config <>
        braces (pretty "println!(\"Incorrect usage\");") <> line <>
        rbrace
    where
        genIdxLocCount (lname, (npids,_,_,_,_)) =
            if npids == 0 then pretty "" else
                pretty "let n_" <> pretty (locName lname) <+> pretty "= get_num_from_cmdline" <> (parens . dquotes $ pretty lname) <> pretty ";"

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
                return $ pretty "let mut" <+> pretty (rustifyName name) <+> pretty "= HashMap::new();" <> line <>
                    pretty "for i in 0..n_" <> pretty (locName idxLocName) <> braces (ni <+> pretty (rustifyName name) <> pretty ".insert(i, owl_tmp);")
            else throwError $ UnsupportedSharedIndices "can't have a name shared by multiple PID-parameterized localities"

        genSalt = pretty "let" <+> pretty "salt" <+> pretty "=" <+> pretty "owl_util::gen_rand_bytes(64);" -- use 64 byte salt

        writeConfig pubKeys (loc, (npids, _, ss, _, _)) =
            let configInits = hsep . punctuate comma $
                    (map (\(n,_,_,_) -> pretty (rustifyName n) <+> pretty ":" <+> pretty (rustifyName n) <> (if npids == 0 then pretty "" else pretty ".get(&i).unwrap()") <> pretty ".vec.clone()") ss ++
                     map (\n -> pretty "pk_" <> pretty (rustifyName n) <+> pretty ":" <+> pretty "pk_" <> pretty (rustifyName n) <> pretty ".vec.clone()") pubKeys ++
                     [pretty "salt" <+> pretty ":" <+> pretty "salt" <> pretty ".vec.clone()"]) in
            (if npids == 0 then pretty "" else pretty "for i in 0..n_" <> pretty (locName loc) <+> lbrace) <>
            pretty "let" <+> pretty (locName loc) <> pretty "_config:" <+> pretty (locName loc) <> pretty "_config" <+> pretty "=" <+> pretty "todo!(); //" <+> pretty (locName loc) <> pretty "_config" <+> braces configInits <> pretty ";" <> line <>
            pretty "let" <+> pretty (locName loc) <> pretty "_config_serialized: std::string::String" <+> pretty "=" <+>
                    pretty "todo!(); // serde_json::to_string" <> parens (pretty "&" <> pretty (locName loc) <> pretty "_config") <> pretty ".unwrap();" <> line <>
            pretty "let mut" <+> pretty (locName loc) <> pretty "_f" <+> pretty "=" <+>
                pretty "fs::File::create(format!(\"{}/{}" <> (if npids == 0 then pretty "" else pretty "_{}") <> pretty ".owl_config\", &args[2]," <+>
                    dquotes (pretty (locName loc)) <> (if npids == 0 then pretty "" else pretty ",i") <> pretty ")).expect(\"Can't create config file\");" <> line <>
            pretty (locName loc) <> pretty "_f" <> pretty ".write_all" <> parens (pretty (locName loc) <> pretty "_config_serialized.as_bytes()")
                                <> pretty ".expect(\"Can't write config file\");" <>
            (if npids == 0 then pretty "" else rbrace)

        genRunLoc (loc, nSidArgs) =
            let body = genRunLocBody loc nSidArgs in
            -- pretty "if" <+> (hsep . punctuate (pretty " && ") . map pretty $ 
            --         ["args.len() >= 4", "args.index(1).as_str().into_rust_str() == \"run\"", "args.index(2).as_str().into_rust_str() == \"" ++ loc ++ "\""]) <>                
            pretty "if" <+> (hsep . punctuate (pretty " && ") . map pretty $ ["args.len() >= 4", "args[1] == \"run\"", "args[2] == \"" ++ loc ++ "\""]) <>
                braces body <> pretty "else"
        genRunLocBody loc nSidArgs =
            pretty "let mut s =" <+> pretty (locName loc) <> pretty "::init_" <> pretty (locName loc) <>
                -- parens (pretty "&args.index(3)") <> pretty ";" <> line <>
                parens (pretty "&String::from_rust_string(args[3].clone()).as_str()") <> pretty ";" <> line <>
            pretty "println!(\"Waiting for 5 seconds to let other parties start...\");" <> line <>
            pretty "thread::sleep(Duration::new(5, 0));" <> line <>
            pretty "println!(\"Running" <+> pretty loc <> pretty "_main() ...\");" <> line <>
            pretty "let now = Instant::now();" <> line <>
            pretty "let res = s." <> pretty (rustifyName loc) <> pretty "_main" <> tupled (pretty "todo!(/* itree token */)" : [pretty i | i <- [1..nSidArgs]]) <> pretty ";" <> line <>
            pretty "let elapsed = now.elapsed();" <> line <>
            pretty "println!" <> parens (dquotes (pretty loc <+> pretty "returned ") <> pretty "/*" <> pretty "," <+> pretty "res" <> pretty "*/") <> pretty ";" <> line <>
            pretty "println!" <> parens (dquotes (pretty "Elapsed: {:?}") <> pretty "," <+> pretty "elapsed") <> pretty ";"


-------------------------------------------------------------------------------------------
-- Decl extraction

extractDecl :: Decl -> ExtractionMonad (Doc ann, Doc ann)
extractDecl dcl =
    case dcl^.val of
        DeclStruct name fields -> do
            let (_, fields') = unsafeUnbind fields
            extractStruct name fields'
        DeclEnum name cases -> do
            let (_, cases') = unsafeUnbind cases
            extractEnum name cases'
        DeclTy name topt -> do
            case topt of
              Nothing -> do
                typeLayouts %= M.insert (rustifyName name) (LBytes 0) -- Replaced later when instantiated
                return $ (pretty "", pretty "")
              Just t -> do
                lct <- layoutCTy . doConcretifyTy $ t
                typeLayouts %= M.insert (rustifyName name) lct
                return $ (pretty "", pretty "")
        _ -> return $ (pretty "", pretty "") -- Other decls are handled elsewhere

extractDecls' :: [Decl] -> ExtractionMonad (Doc ann, Doc ann)
extractDecls' [] = return $ (pretty "", pretty "")
extractDecls' (d:ds) = do
    (dExtracted, sExtracted) <- extractDecl d
    (dsExtracted, ssExtracted) <- extractDecls' ds
    return $ (dExtracted <> line <> line <> dsExtracted, sExtracted <> line <> line <> ssExtracted)

extractDecls :: [Decl] -> ExtractionMonad (Doc ann)
extractDecls ds = do
    (globalDecls, locDecls, sharedNames, pubKeys) <- sortDecls ds
    (globalsExtracted, globalSpecsExtracted) <- extractDecls' globalDecls
    (sidArgMap, locsExtracted, specsExtracted) <- extractLocs pubKeys locDecls
    p <- preamble
    ep <- entryPoint locDecls sharedNames pubKeys sidArgMap
    return (
        p                       <> line <> line <> line <> line <> 
        pretty "// ------------------------------------" <> line <>
        pretty "// ---------- SPECIFICATIONS ----------" <> line <>
        pretty "// ------------------------------------" <> line <> line <>
        globalSpecsExtracted    <> line <> line <>
        specsExtracted          <> line <> line <> line <> line <>
        pretty "// ------------------------------------" <> line <>
        pretty "// ---------- IMPLEMENTATIONS ---------" <> line <>
        pretty "// ------------------------------------" <> line <> line <>
        globalsExtracted        <> line <> line <>
        locsExtracted           <> line <> line <>
        pretty "// ------------------------------------" <> line <>
        pretty "// ------------ ENTRY POINT -----------" <> line <>
        pretty "// ------------------------------------" <> line <> line <>
        ep                      <> line <> line <>
        pretty "} // verus!"    <> line <> line)


preamble :: ExtractionMonad (Doc ann)
preamble = do
    c <- showAEADCipher
    h <- showHMACMode
    return $ vsep $ map pretty
        [   "#![allow(unused_imports)]",
            "#![allow(unused_imports)]",
            "#![allow(non_camel_case_types)]",
            "#![allow(non_snake_case)]",
            "#![allow(non_upper_case_globals)]",
            "pub use vstd::{*, prelude::*, vec::*, seq::*, option::*, modes::*, slice::*, string::*};",
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
            "pub mod speclib;",
            "#[macro_use] pub use crate::speclib::{*, itree::*};",
            "pub mod execlib;",
            "#[macro_use] pub use crate::execlib::{*};",
            "pub mod owl_aead;",
            "pub mod owl_hmac;",
            "pub mod owl_pke;",
            "pub mod owl_util;",
            "pub mod owl_dhke;",
            "pub mod owl_hkdf;",
            "verus!{",
            "pub spec const CIPHER: owl_aead::Mode = " ++ c ++ ";",
            "pub spec const KEY_SIZE: usize = owl_aead::spec_key_size(CIPHER);",
            "pub spec const TAG_SIZE: usize = owl_aead::spec_tag_size(CIPHER);",
            "pub spec const NONCE_SIZE: usize = owl_aead::spec_nonce_size(CIPHER);",
            "pub spec const HMAC_MODE: owl_hmac::Mode = " ++ h ++ ";",
            "pub const fn cipher() -> (r:owl_aead::Mode) ensures r == CIPHER { " ++ c ++ "}",
            "pub const fn key_size() -> (r:usize) ensures r == KEY_SIZE { owl_aead::key_size(cipher()) }",
            "pub const fn tag_size() -> (r:usize) ensures r == TAG_SIZE { owl_aead::tag_size(cipher()) }",
            "pub const fn nonce_size() -> (r:usize) ensures r == NONCE_SIZE { owl_aead::nonce_size(cipher()) }",
            "pub const fn hmac_mode() -> (r:owl_hmac::Mode) ensures r == HMAC_MODE { " ++ h ++ " }"
        ] ++
        [   owlOpsTraitDef,
            owlOpsTraitImpls,
            owl_msgDef,
            owl_outputDef,
            owl_inputDef,
            owl_sampleImplDef,
            owl_miscFns
        ]
    where
        owlOpsTraitDef = vsep $ map pretty [
                "trait OwlOps {",
                    -- "fn owl_output/*<A>*/(&self, /*t: &mut Tracked<ITreeToken<A,Endpoint>>, */ dest_addr: &StrSlice, ret_addr: &StrSlice);",
                    "fn owl_enc(&self, key: &[u8], iv: &[u8]) -> Vec<u8>;",
                    "fn owl_dec(&self, key: &[u8]) -> Option<Vec<u8>>;",
                    -- "fn owl_eq(&self, other: &Self) -> bool;",
                    --     "where Self: PartialEq",
                    -- "{",
                    --     "self == other",
                    -- "}",
                    "fn owl_length(&self) -> usize;",
                    "fn owl_mac(&self, key: &[u8]) -> Vec<u8>;",
                    "fn owl_mac_vrfy(&self, key: &[u8], value: &[u8]) -> Option<Vec<u8>>;",
                    "fn owl_pkenc(&self, pubkey: &[u8]) -> Vec<u8>;",
                    "fn owl_pkdec(&self, privkey: &[u8]) -> Vec<u8>;",
                    "fn owl_sign(&self, privkey: &[u8]) -> Vec<u8>;",
                    "fn owl_vrfy(&self, pubkey: &[u8], signature: &[u8]) -> Option<Vec<u8>>;",
                    "fn owl_dh_combine(&self, others_pk: &[u8]) -> Vec<u8>;",
                    "fn owl_extract_expand_to_len(&self, salt: &[u8], len: usize) -> Vec<u8>;",
                    "fn owl_xor(&self, other: &[u8]) -> Vec<u8>;",
                "}"
            ]
        owlOpsTraitImpls = vsep $ map pretty [
                "impl OwlOps for &[u8] {",
                    -- "fn owl_output/*<A>*/(&self, /*t: &mut Tracked<ITreeToken<A,Endpoint>>, */ dest_addr: &StrSlice, ret_addr: &StrSlice) {",
                    --     "output(/*t,*/ self, dest_addr, ret_addr);",
                    -- "}",
                    -- "#[verifier(external_body)] fn owl_eq(&self, other: &&[u8]) -> bool {",
                    --     "self == other",
                    -- "}",
                    "#[verifier(external_body)] fn owl_enc(&self, key: &[u8], iv: &[u8]) -> Vec<u8> {",
                        "match owl_aead::encrypt_combined(cipher(), key, self, iv) {",
                            "Ok(c) => c,",
                            "Err(e) => {",
                                "// dbg!(e);",
                                "Vec { vec: vec![] }",
                            "}",
                        "}",
                    "}",
                    "#[verifier(external_body)] fn owl_dec(&self, key: &[u8]) -> Option<Vec<u8>> {",
                        "match owl_aead::decrypt_combined(cipher(), slice_subrange(&key, 0, key_size()), self, slice_subrange(&key, key_size(), key.len())) {",
                            "Ok(p) => Some(p),",
                            "Err(e) => {",
                                "// dbg!(e);",
                                "None",
                            "}",
                        "}",
                    "}",
                    "#[verifier(external_body)] fn owl_length(&self) -> usize {",
                        "self.len()",
                    "}",
                    "fn owl_mac(&self, key: &[u8]) -> Vec<u8> {",
                        "owl_hmac::hmac(hmac_mode(), key, self, None)",
                    "}",
                    "fn owl_mac_vrfy(&self, key: &[u8], value: &[u8]) -> Option<Vec<u8>> {",
                        "if owl_hmac::verify(hmac_mode(), key, self, &value, None) {",
                            "Some(slice_to_vec(self))",
                        "} else {",
                            "None",
                        "}",
                    "}",
                    "fn owl_pkenc(&self, pubkey: &[u8]) -> Vec<u8> {",
                        "owl_pke::encrypt(pubkey, self)",
                    "}",
                    "fn owl_pkdec(&self, privkey: &[u8]) -> Vec<u8> {",
                        "owl_pke::decrypt(privkey, self)",
                    "}",
                    "fn owl_sign(&self, privkey: &[u8]) -> Vec<u8> {",
                        "owl_pke::sign(privkey, self)",
                    "}",
                    "fn owl_vrfy(&self, pubkey: &[u8], signature: &[u8]) -> Option<Vec<u8>> {",
                        "if owl_pke::verify(pubkey, signature, self) {",
                            "Some(slice_to_vec(self))",
                        "} else {",
                            "None",
                        "}",
                    "}",
                    "fn owl_dh_combine(&self, others_pk: &[u8]) -> Vec<u8> {",
                        "owl_dhke::ecdh_combine(self, others_pk)",
                    "}",
                    "fn owl_extract_expand_to_len(&self, salt: &[u8], len: usize) -> Vec<u8> {",
                        "owl_hkdf::extract_expand_to_len(self, salt, len)",
                    "}",
                    "#[verifier(external_body)] fn owl_xor(&self, other: &[u8]) -> Vec<u8> {",
                        "{let c = Vec { vec: self.iter().zip(other).map(|(x, y)| x ^ y).collect() }; c}",
                    "}",
                "}",
                -- "impl OwlOps for Vec<u8> {",
                --     "fn owl_output<A>(&self, t: &mut Tracked<ITreeToken<A,Endpoint>>, dest_addr: &StrSlice, ret_addr: &StrSlice) { (&self.as_slice()).owl_output(t, dest_addr, ret_addr) }",
                --     "fn owl_enc(&self, key: &[u8], iv: &[u8]) -> Vec<u8> { (&self.as_slice()).owl_enc(key, iv) }",
                --     "fn owl_dec(&self, key: &[u8]) -> Option<Vec<u8>> { (&self.as_slice()).owl_dec(key) }",
                --     -- "fn owl_eq(&self, other: &Self) -> bool { self.as_slice().owl_eq(&other.as_slice()) }",
                --     "fn owl_length(&self) -> usize { self.len() }",
                --     "fn owl_mac(&self, key: &[u8]) -> Vec<u8> { (&self.as_slice()).owl_mac(key) }",
                --     "fn owl_mac_vrfy(&self, key: &[u8], value: &[u8]) -> Option<Vec<u8>> { (&self.as_slice()).owl_mac_vrfy(key, value) }",
                --     "fn owl_pkenc(&self, pubkey: &[u8]) -> Vec<u8> { (&self.as_slice()).owl_pkenc(pubkey) }",
                --     "fn owl_pkdec(&self, privkey: &[u8]) -> Vec<u8> { (&self.as_slice()).owl_pkdec(privkey) }",
                --     "fn owl_sign(&self, privkey: &[u8]) -> Vec<u8> { (&self.as_slice()).owl_sign(privkey) }",
                --     "fn owl_vrfy(&self, pubkey: &[u8], signature: &[u8]) -> Option<Vec<u8>> { (&self.as_slice()).owl_vrfy(pubkey, signature) } ",
                --     "fn owl_dh_combine(&self, others_pk: &[u8]) -> Vec<u8> { (&self.as_slice()).owl_dh_combine(others_pk) }",
                --     "fn owl_extract_expand_to_len(&self, salt: &[u8], len: usize) -> Vec<u8> { (&self.as_slice()).owl_extract_expand_to_len(salt, len) }",
                --     "fn owl_xor(&self, other: &[u8]) -> Vec<u8> { (&self.as_slice()).owl_xor(other) }",
                -- "}",
                ""
            ]
        owl_msgDef = vsep $ map pretty [
                "// #[derive(Serialize, Deserialize, Debug)] // TODO incorporate real parsing/marshaling",
                "/* pub struct msg {",
                    "ret_addr: std::string::String,",
                    "payload: std::vec::Vec<u8>",
                "} */"
            ]
        owl_outputDef = vsep $ map pretty [
                "#[verifier(external_body)]",
                "pub fn owl_output<A>(t: &mut Tracked<ITreeToken<A,Endpoint>>, x: &[u8], dest_addr: &StrSlice, ret_addr: &StrSlice)",
                    "requires old(t)@@.is_output(x@, endpoint_of_addr(dest_addr.view()))",
                    "ensures  t@@ === old(t)@@.give_output()",
                "{",
                    "/*",
                    "let msg = msg { ret_addr: std::string::String::from(ret_addr.into_rust_str()), payload: std::vec::Vec::from(x) };",
                    "let serialized = serde_json::to_vec(&msg).unwrap();",
                    "let mut stream = TcpStream::connect(dest_addr.into_rust_str()).unwrap();",
                    "stream.write_all(&serialized).unwrap();",
                    "stream.flush().unwrap();",
                    "*/",
                    "todo!()",
                "}"
            ]
        owl_inputDef = vsep $ map pretty [
                "#[verifier(external_body)]",
                "pub fn owl_input<A>(t: &mut Tracked<ITreeToken<A,Endpoint>>, /*listener: &TcpListener*/) -> (ie:(Vec<u8>, String))", 
                    "requires old(t)@@.is_input()",
                    "ensures  t@@ === old(t)@@.take_input(ie.0@, endpoint_of_addr(ie.1.view()))",
                "{",
                    "/*",
                    "let (mut stream, _addr) = listener.accept().unwrap();",
                    "let mut reader = io::BufReader::new(&mut stream);",
                    "let received: std::vec::Vec<u8> = reader.fill_buf().unwrap().to_vec();",
                    "reader.consume(received.len());",
                    "let msg : msg = serde_json::from_slice(&received).expect(\"Couldn't parse input\");",
                    "(Vec { vec: msg.payload }, String::from_rust_string(msg.ret_addr))",
                    "*/",
                    "todo!()",
                "}"
            ]
        owl_sampleImplDef = vsep $ map pretty [
                "#[verifier(external_body)]",
                "pub fn owl_sample<A>(t: &mut Tracked<ITreeToken<A,Endpoint>>, n: usize) -> (res:Vec<u8>)", 
                    "requires old(t)@@.is_sample(n)",
                    "ensures  t@@ === old(t)@@.get_sample(res@)",
                "{",
                    "owl_util::gen_rand_bytes(n)",
                "}"
            ]
        owl_miscFns = vsep $ map pretty [
                "/* pub fn get_num_from_cmdline(loc_prompt: &str) -> usize {",
                    "let mut input_text = std::string::String::new();",
                    "println!(\"Enter number of {loc_prompt} to generate: \");",
                    "io::stdin()",
                        ".read_line(&mut input_text)",
                        ".expect(\"failed to read from stdin\");",
                    "let n = input_text.trim().parse::<usize>().expect(\"not an int\");",
                    "n",
                "} */",
                ""
            ]

extract :: String -> [Decl] -> IO (Either ExtractionError (Doc ann))
extract path dcls = runExtractionMonad (initEnv path) $ extractDecls dcls
