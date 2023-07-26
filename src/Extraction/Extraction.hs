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
import System.IO
import qualified Text.Parsec as P
import qualified Parse as OwlP
import System.FilePath (takeFileName, (</>))
import qualified TypingBase as TB
import ExtractionBase
import qualified SpecExtraction as Spec


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
            _ -> throwError $ CantLayoutType (CTDataWithLength aexp)
    in
    helper aexp
layoutCTy (CTOption ct) = do
    lct <- layoutCTy ct
    return $ LEnum "builtin_option" $ M.fromList [("Some", (1, Just $ lct)), ("None", (2, Just $ LBytes 0))]
layoutCTy (CTConst p) = do
    p' <- flattenPath p
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

genOwlOpsImpl :: String -> Doc ann
genOwlOpsImpl name = pretty
    "impl OwlOps for" <+> pretty name <+> (braces . vsep $ map pretty [
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

extractStruct :: String -> [(String, Ty)] -> ExtractionMonad (Doc ann)
extractStruct owlName owlFields = do
    let name = rustifyName owlName
    -- liftIO $ print name
    let parsingOutcomeName = name ++ "_ParsingOutcome"
    let typeDef = pretty "pub type" <+> pretty name <+> pretty "= (Rc<Vec<u8>>," <+> pretty parsingOutcomeName <> pretty ");"
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
                        pretty "construct_" <> (pretty . rustifyName) owlName <>
                            (parens . hsep . punctuate comma . map (\(t,a) -> pretty "&" <> pretty a <> (case t of
                                ADT _ -> pretty ".0"
                                _ -> pretty ""))
                            $ args)
                        ))) :
                map (\(owlField, _) -> (owlField, (rustifyName owlName, RcVecU8, \args -> do
                    case args of
                      (ADT _, arg) : _ -> do
                        return $ (Nothing, show $
                            pretty "Rc::new(get_" <> (pretty . rustifyName) owlField <> pretty "_" <> (pretty . rustifyName) owlName <> parens (pretty "&mut" <+> pretty arg) <> pretty ".to_owned())")
                      (VecU8, arg) : _ -> do
                        return $ (Just (arg, owlName), show $
                            pretty "Rc::new(get_" <> (pretty . rustifyName) owlField <> pretty "_" <> (pretty . rustifyName) owlName <>
                                parens (pretty "&" <+> pretty owlName) <> pretty ".to_owned())")
                      (RcVecU8, arg) : _ -> do
                        return $ (Just (arg, owlName), show $
                            pretty "Rc::new(get_" <> (pretty . rustifyName) owlField <> pretty "_" <> (pretty . rustifyName) owlName <>
                                parens (pretty "&" <+> pretty owlName) <> pretty ".to_owned())")
                      _ -> throwError $ TypeError $ "attempt to get from " ++ owlName ++ " with bad args"
                ))) owlFields

        genStructParsingOutcomeDef parsingOutcomeName layoutFields = return $
            pretty "#[derive(PartialEq, Eq, Debug)]" <> line <>
            pretty "pub enum" <+> pretty parsingOutcomeName <+>
            vsep [  lbrace,
                    pretty "Success" <> parens (hsep $ punctuate comma $ replicate (length layoutFields + 1) $ pretty "usize") <> comma,
                    pretty "Failure" <> comma,
                    rbrace]

        genLenValidFnDef name layoutFields =
            let fieldCheckers = map fieldChecker layoutFields in
            let startsPrettied = hsep $ punctuate comma (map (\(n,_) -> pretty "start_" <> pretty n) layoutFields ++ [pretty "i"]) in
            return $ pretty "pub fn" <+> pretty "len_valid_" <> pretty name <> parens (pretty "arg: &[u8]") <+>
                pretty " -> Option" <> (angles . parens . hsep . punctuate comma $ [pretty "usize" | _ <- [0..(length layoutFields)]]) <+> lbrace <> line <>
            pretty "let mut i = 0;" <> line <>
            vsep fieldCheckers <> line <>
            pretty "Some" <> (parens . parens $ startsPrettied) <> line <>
            rbrace
        fieldChecker (n, l) = case l of
            LBytes nb    ->
                pretty "let start_" <> pretty n <+> pretty "= i;" <> line <>
                pretty "if" <+> pretty "arg.len() - i" <+> pretty "<" <+> pretty nb <+> lbrace <> line <>
                pretty "return None;" <> line <>
                rbrace <> line <>
                pretty "i +=" <+> pretty nb <> pretty ";"
            LStruct sn sfs ->
                pretty "let start_" <> pretty n <+> pretty "= i;" <> line <>
                pretty "match" <+> pretty "len_valid_" <> pretty sn <> parens (pretty "&arg[i..]") <+> lbrace <> line <>
                pretty "Some" <> (parens . parens . hsep . punctuate comma $ [pretty "_" | _ <- [0..(length sfs - 1)]] ++ [pretty "l"]) <+> pretty "=>" <+> braces (pretty "i += l;") <> line <>
                pretty "None => " <> braces (pretty "return None;") <> line <>
                rbrace
            LEnum en _   ->
                pretty "let start_" <> pretty n <+> pretty "= i;" <> line <>
                pretty "match" <+> pretty "len_valid_" <> pretty en <> parens (pretty "&arg[i..]") <+> lbrace <> line <>
                pretty "Some(l) => " <> braces (pretty "i += l;") <> line <>
                pretty "None => " <> braces (pretty "return None;") <> line <>
                rbrace

        genParseFnDef name parsingOutcomeName layout layoutFields = return $
            pretty "pub fn" <+> pretty "parse_into_" <> pretty name <> parens (pretty "arg: &mut" <+> pretty name) <+> lbrace <> line <>
                pretty "if arg.1 ==" <+> pretty parsingOutcomeName <> pretty "::Failure" <+> lbrace <> line <>
                    pretty "match len_valid_" <> pretty name <> parens (pretty "&arg.0[..]") <+> lbrace <> line <>
                    pretty "Some" <> (parens . parens . hsep . punctuate comma $ [pretty "idx_" <> pretty j | j <- [0..(length layoutFields)]]) <+>
                        pretty "=>" <+> braces (
                            pretty "arg.1 =" <+> pretty parsingOutcomeName <> pretty "::Success" <>
                                (parens . hsep . punctuate comma $ [pretty "idx_" <> pretty j | j <- [0..(length layoutFields)]]) <>
                            pretty ";"
                        ) <> line <>
                    pretty "None => " <> braces (
                            pretty "arg.0 =" <+> pretty "Rc::new(vec![0;" <+> pretty (lenLayoutFailure layout) <> pretty "]);" <> line <>
                            pretty "arg.1 =" <+> pretty parsingOutcomeName <> pretty "::Failure;"
                        ) <> line <>
                    rbrace <> line <>
                rbrace <> line <>
            rbrace


        genConstructorDef name parsingOutcomeName layout layoutFields = do
            let argsPrettied = hsep $ punctuate comma $ map (\(n,_) -> pretty "arg_" <> pretty n <> pretty ": &[u8]") layoutFields
            let startsPrettied = hsep $ punctuate comma (map (\(n,_) -> pretty "start_" <> pretty n) layoutFields ++ [pretty "i"])
            let checkAndExtenders = map (\(n,l) -> checkAndExtender (lenLayoutFailure layout) parsingOutcomeName n l) layoutFields
            return $ pretty "pub fn" <+> pretty "construct_" <> pretty name <> parens argsPrettied <+> pretty "->" <+> pretty name <+> lbrace <> line <>
                pretty "let mut v = vec![];" <> line <>
                pretty "let mut i = 0;" <> line <>
                vsep checkAndExtenders <> line <>
                pretty "let res = (Rc::new(v)," <+> pretty parsingOutcomeName <> pretty "::Success" <> parens startsPrettied <> pretty ");" <> line <>
                pretty "res" <> line <>
                rbrace
        checkAndExtender lenFailure parsingOutcomeName n l =
            let structEnumChecker dn = pretty "len_valid_" <> pretty dn <> parens (pretty "arg_" <> pretty n) <+> pretty " == None" in
            let checker = case l of
                    LBytes i     -> pretty "arg_" <> pretty n <> pretty ".len()" <+> pretty "!=" <+> pretty i
                    LStruct sn _ -> structEnumChecker sn
                    LEnum en _   -> structEnumChecker en in
            pretty "let start_" <> pretty n <+> pretty "= i;" <> line <>
            pretty "if" <+> checker <+> lbrace <> line <>
            pretty "return" <+> parens (pretty "Rc::new(vec![0;" <+> pretty lenFailure <> pretty "])," <+> pretty parsingOutcomeName <> pretty "::Failure") <> pretty ";" <> line <>
            rbrace <> line <>
            pretty "v.extend" <> parens (pretty "arg_" <> pretty n) <> pretty ";" <> line <>
            pretty "i += " <> pretty "arg_" <> pretty n <> pretty ".len();"

        genSelectorDefs name parsingOutcomeName layoutFields = do
            let (_, layoutOffsets) = mapAccumL (\(o,i) (n,l) -> let nextO = o + lenLayoutFailure l in ((nextO, i + 1), (n,l,o,nextO,i))) (0,0) layoutFields
            return $ map (genSelectorDef name parsingOutcomeName (length layoutFields)) layoutOffsets

        genSelectorDef :: String -> String -> Int -> (String, Layout, Int, Int, Int) -> Doc ann
        genSelectorDef name parsingOutcomeName numFields (fieldName, fieldLayout, failOffset, failNextOffset, structIdx) =
            let success_pattern = pretty parsingOutcomeName <> pretty "::Success" <> (parens . hsep . punctuate comma $ [pretty "idx_" <> pretty j | j <- [0..numFields]]) in
            -- return $
            pretty "pub fn" <+> pretty "get_" <> pretty fieldName <> pretty "_" <> pretty name <> parens (pretty "arg: &" <+> pretty name) <+> pretty "->" <+> pretty "&[u8]" <+> lbrace <> line <>
            pretty "// parse_into_" <> pretty name <> parens (pretty "arg") <> pretty ";" <> line <>
            pretty "match arg.1 {" <> line <>
            success_pattern <+> pretty "=>" <+>
                pretty "&arg.0[idx_" <> pretty structIdx <> pretty "..idx_" <> pretty (structIdx + 1) <> pretty "]," <> line <>
            pretty parsingOutcomeName <> pretty "::Failure => &arg.0[" <> pretty failOffset <> pretty ".." <> pretty failNextOffset <> pretty "]" <> line <>
            pretty "}" <> line <>
            pretty "}"



extractEnum :: String -> [(String, Maybe Ty)] -> ExtractionMonad (Doc ann)
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
    let typeDef = tagsComment <> line <> pretty "pub type" <+> pretty name <+> pretty "= (Rc<Vec<u8>>," <+> pretty parsingOutcomeName <> pretty ");"
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
                    pretty "construct_" <> (pretty . rustifyName) owlName <> pretty "_" <> (pretty . rustifyName) owlCase <>
                        (parens . hsep . punctuate comma . map (\(t,a) -> pretty "&" <> pretty a <> (case t of
                                ADT _ -> pretty ".0"
                                _ -> pretty "")) $ args)
                )))) $ M.assocs owlCases

        genEnumParsingOutcomeDef parsingOutcomeName = return $
            pretty "#[derive(PartialEq, Eq, Debug)]" <> line <>
            pretty "pub enum" <+> pretty parsingOutcomeName <+>
            vsep [  lbrace,
                    pretty "Success" <> comma,
                    pretty "Failure" <> comma,
                    rbrace]

        genLenValidFnDef name layoutCases =
            let caseCheckers = map caseChecker $ M.assocs layoutCases in
            return $ pretty "pub fn" <+> pretty "len_valid_" <> pretty name <> parens (pretty "arg: &[u8]") <+>
                pretty " -> Option<usize>" <+> lbrace <> line <>
            pretty "if arg.len() < 1 { return None; } else " <> line <>
            vsep (punctuate (pretty " else ") caseCheckers) <> line <>
            pretty "else { return None; }" <> line <>
            rbrace
        caseChecker (t, (n, l)) = case l of
            Just (LBytes nb)    ->
                pretty "if arg[0] ==" <+> pretty n <+> pretty "&&" <+> pretty "arg.len() >=" <+> pretty (1 + nb) <+>
                braces (pretty " return Some(" <+> pretty (1 + nb) <> pretty "); ")
            Just (LStruct sn sfs) ->
                pretty "if arg[0] ==" <+> pretty n <+> braces (
                    pretty "match" <+> pretty "len_valid_" <> pretty sn <> parens (pretty "&arg[1..]") <+> lbrace <> line <>
                    pretty "Some" <> (parens . parens . hsep . punctuate comma $ [pretty "_" | _ <- [0..(length sfs - 1)]] ++ [pretty "l"]) <+>
                        pretty "=>" <+> braces (pretty "return Some(1 + l);") <> line <>
                    pretty "None => " <> braces (pretty "return None;") <> line <>
                    rbrace
                )
            Just (LEnum en _)   ->
                pretty "if arg[0] ==" <+> pretty n <+> braces (
                    pretty "let start_" <> pretty n <+> pretty "= i;" <> line <>
                    pretty "match" <+> pretty "len_valid_" <> pretty en <> parens (pretty "&arg[1..]") <+> lbrace <> line <>
                    pretty "Some(l) => " <> braces (pretty "return Some(1 + l);") <> line <>
                    pretty "None => " <> braces (pretty "return None;") <> line <>
                    rbrace
                )
            Nothing ->
                pretty "if arg[0] ==" <+> pretty n <+> braces ( pretty "return Some(arg.len());" )

        genParseFnDef name parsingOutcomeName layout = return $
            pretty "pub fn" <+> pretty "parse_into_" <> pretty name <> parens (pretty "arg: &mut" <+> pretty name) <+> lbrace <> line <>
                pretty "if arg.1 ==" <+> pretty parsingOutcomeName <> pretty "::Failure" <+> lbrace <> line <>
                    pretty "match len_valid_" <> pretty name <> parens (pretty "&arg.0[..]") <+> lbrace <> line <>
                    pretty "Some(l)" <+>
                        pretty "=>" <+> braces (pretty "arg.1 =" <+> pretty parsingOutcomeName <> pretty "::Success;") <> line <>
                    pretty "None => " <> braces (
                            pretty "arg.0 =" <+> pretty "Rc::new(vec![0;" <+> pretty (lenLayoutFailure layout) <> pretty "]);" <> line <>
                            pretty "arg.1 =" <+> pretty parsingOutcomeName <> pretty "::Failure;"
                        ) <> line <>
                    rbrace <> line <>
                rbrace <> line <>
            rbrace

        genConstructorDefs name parsingOutcomeName layout layoutCases =
            return $ map (genConstructorDef name parsingOutcomeName) $ M.assocs layoutCases

        genConstructorDef :: String -> String -> (String, (Int, Maybe Layout)) -> Doc ann
        genConstructorDef name parsingOutcomeName (tagName, (tag, Just (LBytes 0))) = -- special case for a case with no payload, where the constructor takes no arg
            pretty "pub fn" <+> pretty "construct_" <> pretty name <> pretty "_" <> pretty tagName <> pretty "()" <+> pretty "->" <+> pretty name <+> lbrace <> line <>
                pretty "let mut v = vec![" <> pretty tag <> pretty "u8];" <> line <>
                pretty "let res = (Rc::new(v)," <+> pretty parsingOutcomeName <> pretty "::Success" <> pretty ");" <> line <>
                pretty "res" <> line <>
            rbrace

        genConstructorDef name parsingOutcomeName (tagName, (tag, tagLayout)) =
            -- Failure case for struct is always a zero tag with no payload
            let failureReturn = pretty "return" <+> parens (pretty "Rc::new(vec![0; 1])," <+> pretty parsingOutcomeName <> pretty "::Failure") <> pretty ";" in
            let checkAndExtender = case tagLayout of
                    Just (LBytes nb)    ->
                        pretty "if" <+> pretty "arg.len()" <+> pretty "<" <+> pretty nb <+> braces failureReturn <> line <>
                        pretty "v.extend" <> parens (pretty "&arg[.." <> pretty nb <> pretty "]") <> pretty ";" <> line
                    Just (LStruct sn sfs) ->
                        pretty "match" <+> pretty "len_valid_" <> pretty sn <> parens (pretty "arg") <+> lbrace <> line <>
                        pretty "Some" <> (parens . parens . hsep . punctuate comma $ [pretty "_" | _ <- [0..(length sfs - 1)]] ++ [pretty "l"]) <+>
                            pretty "=>" <+> braces (pretty "v.extend" <> parens (pretty "&arg[..l]") <> pretty ";") <> line <>
                        pretty "None => " <> braces failureReturn <> line <>
                        rbrace
                    Just (LEnum en _)   ->
                        pretty "match" <+> pretty "len_valid_" <> pretty en <> parens (pretty "arg") <+> lbrace <> line <>
                        pretty "Some(l) => " <> braces (pretty "v.extend" <> parens (pretty "&arg[..l]") <> pretty ";") <> line <>
                        pretty "None => " <> braces failureReturn <> line <>
                        rbrace
                    Nothing ->
                        pretty "v.extend(&arg[..]);"
                in
            pretty "pub fn" <+> pretty "construct_" <> pretty name <> pretty "_" <> pretty tagName <> parens (pretty "arg: &[u8]") <+> pretty "->" <+> pretty name <+> lbrace <> line <>
                pretty "let mut v = vec![" <> pretty tag <> pretty "u8];" <> line <>
                checkAndExtender <> line <>
                pretty "let res = (Rc::new(v)," <+> pretty parsingOutcomeName <> pretty "::Success" <> pretty ");" <> line <>
                pretty "res" <> line <>
            rbrace

-------------------------------------------------------------------------------------------
-- Code generation

extractCryptOp :: M.Map String RustTy -> CryptOp -> [AExpr] -> ExtractionMonad (RustTy, Doc ann, Doc an)
extractCryptOp binds op owlArgs = do
    argsPretties <- mapM (extractAExpr binds . view val) owlArgs
    let preArgs = foldl (\p (_,s,_) -> p <> s) (pretty "") argsPretties
    let args = map (\(r, _, p) -> (r, show p)) argsPretties
    (rt, str) <- case (op, args) of
        (CHash p _ n, [(_,x)]) -> do 
            roname <- flattenPath p 
            orcls <- use oracles
            case orcls M.!? roname of
                Nothing -> throwError $ TypeError "unrecognized random oracle"
                Just outLen -> do
                    return (VecU8, x ++ ".owl_extract_expand_to_len(&self.salt, " ++ outLen ++ ")")
        (CPRF s, _) -> do throwError $ ErrSomethingFailed $ "TODO implement crypto op: " ++ show op
        (CAEnc, [(_,k), (_,x)]) -> do return (VecU8, x ++ ".owl_enc(&" ++ k ++ ")")
        (CADec, [(_,k), (_,x)]) -> do return (Option VecU8, x ++ ".owl_dec(&" ++ k ++ ")")
        (CAEncWithNonce p (sids, pids), _) -> do throwError $ ErrSomethingFailed $ "TODO implement crypto op: " ++ show op
        (CADecWithNonce, _) -> do throwError $ ErrSomethingFailed $ "TODO implement crypto op: " ++ show op
        (CPKEnc, [(_,k), (_,x)]) -> do return (VecU8, x ++ ".owl_pkenc(&" ++ k ++ ")")
        (CPKDec, [(_,k), (_,x)]) -> do return (VecU8, x ++ ".owl_pkdec(&" ++ k ++ ")")
        (CMac, [(_,k), (_,x)]) -> do return (VecU8, x ++ ".owl_mac(&" ++ k ++ ")")
        (CMacVrfy, [(_,k), (_,x), (_,v)]) -> do return (Option VecU8, x ++ ".owl_mac_vrfy(&" ++ k ++ ", &" ++ v ++ ")")
        (CSign, [(_,k), (_,x)]) -> do return (VecU8, x ++ ".owl_sign(&" ++ k ++ ")")
        (CSigVrfy, [(_,k), (_,x), (_,v)]) -> do return (Option VecU8, x ++ ".owl_vrfy(&" ++ k ++ ", &" ++ v ++ ")")
        (_, _) -> do throwError $ TypeError $ "got bad args for crypto op: " ++ show op ++ "(" ++ show args ++ ")"
    return (rt, preArgs, pretty str)


extractAExpr :: M.Map String RustTy -> AExprX -> ExtractionMonad (RustTy, Doc ann, Doc ann)
extractAExpr binds (AEVar _ owlV) = do
    let v = rustifyName . show $ owlV
    case binds M.!? v of
      Nothing -> do
        debugPrint $ "failed to find " ++ show v ++ " in binds: " ++ show binds
        return (VecU8, pretty "", pretty v)
      Just RcVecU8 -> return (RcVecU8, pretty "", pretty "Rc::clone" <> parens (pretty "&" <> pretty v))
      Just rt -> return (rt, pretty "", pretty v)
extractAExpr binds (AEApp owlFn fparams owlArgs) = do
    fs <- use funcs
    argsPretties <- mapM (extractAExpr binds . view val) owlArgs
    let preArgs = foldl (\p (_,s,_) -> p <> s) (pretty "") argsPretties
    let args = map (\(r, _, p) -> (r, show p)) argsPretties
    fdef <- lookupFunc owlFn
    case fdef of
        Just (rt, f) -> do
            str <- f args
            return (rt, preArgs, pretty str)
        Nothing -> do
            -- adtfs <- use adtFuncs
            adtf <- lookupAdtFunc =<< flattenPath owlFn
            case adtf of
                Just (adt, rt, f) -> do
                    (argvaropt, str) <- f args
                    let s = case argvaropt of
                            Nothing -> pretty ""
                            Just (arg,var) ->
                                pretty "let mut" <+> pretty var <+> pretty "=" <+> parens (pretty arg <> comma <+> pretty adt <> pretty "_ParsingOutcome::Failure") <> pretty ";" <> line <>
                                pretty "parse_into_" <> pretty adt <> parens (pretty "&mut" <+> pretty var) <> pretty ";"
                    return (rt, preArgs <> s, pretty str)
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
                                        return (VecU8, pretty "", (pretty . rustifyName . unignore $ owlV) <>
                                                                pretty ".owl_extract_expand_to_len(&self.salt," <+> pretty outLen <> pretty ")")
                            _ -> throwError $ TypeError $ "incorrect args/params to random oracle function"
                    else throwError $ UndefinedSymbol $ show owlFn
extractAExpr binds (AEString s) = return (VecU8, pretty "", dquotes (pretty s) <> pretty ".as_bytes()")
extractAExpr binds (AEInt n) = return (Number, pretty "", pretty n)
extractAExpr binds (AEGet nameExp) =
    case nameExp ^. val of
        BaseName ([], _) s -> do
            fnameExp <- flattenNameExp nameExp
            return (RcVecU8, pretty "", pretty "Rc::clone" <> parens (pretty "&self." <> pretty (fnameExp)))
        BaseName (sidxs, _) s -> do
            ps <- flattenPath s
            return (RcVecU8, pretty "", pretty "self.get_" <> pretty (rustifyName ps) <> tupled (map (pretty . sidName . show . pretty) sidxs))
        _ -> throwError $ UnsupportedNameExp nameExp
extractAExpr binds (AEGetEncPK nameExp) = do
    fnameExp <- flattenNameExp nameExp
    return (RcVecU8, pretty "", pretty "Rc::clone" <> parens (pretty "&self.pk_" <> pretty fnameExp))
extractAExpr binds (AEGetVK nameExp) = do
    fnameExp <- flattenNameExp nameExp
    return (RcVecU8, pretty "", pretty "Rc::clone" <> parens (pretty "&self.pk_" <> pretty fnameExp))
extractAExpr binds (AEPackIdx idx ae) = extractAExpr binds (ae^.val)
extractAExpr binds (AELenConst s) = do
    lcs <- use lenConsts
    case lcs M.!? (rustifyName s) of
      Nothing -> throwError $ UndefinedSymbol s
      Just n -> return (Number, pretty "", pretty n)



extractExpr :: Locality -> M.Map String RustTy -> CExpr -> ExtractionMonad (M.Map String RustTy, RustTy, Doc ann, Doc ann)
extractExpr loc binds CSkip = return (binds, Unit, pretty "", pretty "()")
extractExpr loc binds (CInput xsk) = do
    let ((x, ev), k) = unsafeUnbind xsk
    let rustX = rustifyName . show $ x
    let rustEv = if show ev == "_" then "_" else rustifyName . show $ ev
    (_, rt', prek, kPrettied) <- extractExpr loc (M.insert rustX RcVecU8 binds) k
    let eWrapped = pretty "Rc::new" <> parens (pretty "temp_" <> pretty rustX)
    let letbinding =
            pretty "let" <+> parens (pretty "temp_" <> pretty rustX <> comma <+> pretty rustEv) <+> pretty "=" <+> pretty "owl_input(&self.listener)" <> pretty ";" <> line <>
            pretty "let" <+> pretty rustX <+> pretty "=" <+> eWrapped <> pretty ";"
    return (binds, rt', pretty "", vsep [letbinding, prek, kPrettied])
extractExpr (Locality myLname myLidxs) binds (COutput ae lopt) = do
    (_, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    l <- case lopt of
        Nothing -> throwError OutputWithUnknownDestination
        Just (EndpointLocality (Locality lname _)) -> do
            plname <- flattenPath lname
            return $ pretty "&" <> pretty plname <> pretty "_addr"
        Just (Endpoint ev) -> return $ pretty "&" <> (pretty . rustifyName . show $ ev)
    pmyLname <- flattenPath myLname
    return $ (binds, Unit, preAe, pretty "&" <> aePrettied <> pretty ".owl_output" <> parens (l <> comma <+> pretty "&" <> pretty (pmyLname) <> pretty "_addr") <> pretty ";")
extractExpr loc binds (CLet e xk) = do
    let (x, k) = unsafeUnbind xk
    let rustX = rustifyName . show $ x
    (_, rt, preE, ePrettied) <- extractExpr loc binds e
    (_, rt', preK, kPrettied) <- extractExpr loc (M.insert rustX (if rt == VecU8 then RcVecU8 else rt) binds) k
    let eWrapped = case rt of
            VecU8 -> pretty "Rc::new" <> parens (pretty "temp_" <> pretty rustX)
            RcVecU8 -> pretty "Rc::clone" <> parens (pretty "&temp_" <> pretty rustX)
            _ -> pretty "temp_" <> pretty rustX
    let letbinding = case e of
            CSkip -> pretty ""
            _ -> pretty "let" <+> pretty "temp_" <> pretty rustX <+> pretty "=" <+> lbrace <+> ePrettied <+> rbrace <> pretty ";" <> line <>
                 pretty "let" <+> pretty rustX <+> pretty "=" <+> eWrapped <> pretty ";"
    return (binds, rt', pretty "", vsep [preE, letbinding, preK, kPrettied])
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
    powlFn <- flattenPath owlFn
    case fs M.!? (powlFn) of
      Nothing -> do
        throwError $ UndefinedSymbol (powlFn)
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
                               RcVecU8 -> pretty "Rc::clone" <> parens (pretty "&temp_" <> pretty rustX)
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
         Just s -> do debugPrint $ pretty "enum casing on" <+> pretty s; return s
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
                       let eWrapped = pretty "Rc::new(caser_tmp.0[1..].to_vec())"
                       return (rt'', pretty b <+> pretty "=>"
                                   <+> braces (pretty "let" <+> pretty rustX <+> pretty "=" <+> eWrapped <> pretty ";" <> line <> preK <> line <> kPrettied))
       branchRt <- case casesPrettiedRts of
         [] -> throwError $ TypeError "case on enum with no cases"
         (b, _) : _ -> return b
       let defaultCase = case branchRt of
             VecU8 -> pretty "vec![0]"
             RcVecU8 -> pretty "Rc::new(vec![0])"
             Bool -> pretty "/* arbitrarily autogenerated */ false"
             Number -> pretty "/* arbitrarily autogenerated */ 0"
             String -> pretty "/* arbitrarily autogenerated */ \"\""
             Unit -> pretty "()"
             ADT s -> pretty "{ let mut tmp = (Rc::new(vec![])," <+> pretty s <> pretty "_ParsingOutcome::Failure); parse_into_" <> pretty s <> pretty "(&mut tmp); tmp }"
             Option _ -> pretty "/* arbitrarily autogenerated */ None"
       let casesPrettied = map snd casesPrettiedRts
       return (binds, branchRt, pretty "", preAe <> braces (
               pretty "let mut caser_tmp" <+> pretty "=" <+> parens (aePrettied <> comma <+> pretty (rustifyName enumOwlName) <> pretty "_ParsingOutcome::Failure") <> pretty ";" <> line <>
               pretty "parse_into_" <> pretty (rustifyName enumOwlName)  <> parens (pretty "&mut caser_tmp") <> pretty ";" <> line <>
               pretty "match caser_tmp.0[0]" <+> braces (
                   vsep casesPrettied <> line <>
                   pretty "_ =>" <+> defaultCase <> comma
               ))
           )
extractExpr loc binds (CTLookup tbl ae) = do
    (rt, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    aeWrapped <- case rt of
            RcVecU8 -> return $ pretty "&" <> aePrettied <> pretty "[..]"
            VecU8 -> return $ pretty "&" <> aePrettied
            _ -> throwError $ ErrSomethingFailed "got wrong arg type for lookup"
    ptbl <- flattenPath tbl
    let tblName = rustifyName ptbl
    return (binds, Option VecU8, preAe, pretty "self." <> pretty tblName <> pretty ".get" <> parens aeWrapped <> pretty ".cloned()")
extractExpr loc binds (CCrypt cryptOp args) = do
    (rt, pre, opPrettied) <- extractCryptOp binds cryptOp args
    return (binds, rt, pre, opPrettied)
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


-- The `owlBody` is expected to *not* be in ANF yet (for extraction purposes)
extractDef :: String -> Locality -> [IdxVar] -> [(DataVar, Embed Ty)] -> Ty -> Expr -> ExtractionMonad (Doc ann)
extractDef owlName loc sidArgs owlArgs owlRetTy owlBody = do
    debugPrint $ pretty ""
    debugPrint $ "Extracting def " ++ owlName 
    let name = rustifyName owlName
    concreteBody <- concretify =<< ANF.anf owlBody
    -- debugPrint $ pretty concreteBody
    specBody <- Spec.extractExpr =<< concretify owlBody
    debugPrint $ specBody
    rustArgs <- mapM rustifyArg owlArgs
    let rustSidArgs = map rustifySidArg sidArgs
    (_, rtb, preBody, body) <- extractExpr loc (M.fromList rustArgs) concreteBody
    decl <- genFuncDecl name rustSidArgs rustArgs rtb
    return $ decl <+> lbrace <> line <> preBody <> line <> body <> line <> rbrace
    where
        genFuncDecl name sidArgs owlArgs rt = do
            let argsPrettied = hsep . punctuate comma $ 
                    pretty "&mut self"
                    : (map (\(a,_) -> pretty a <+> pretty ": usize") sidArgs) 
                    ++ (map extractArg owlArgs)
            return $ pretty "pub fn" <+> pretty name <> parens argsPrettied <+> pretty "->" <+> pretty rt


nameInit :: String -> NameType -> ExtractionMonad (Doc ann)
nameInit s nt = case nt^.val of
    NT_Nonce -> return $ pretty "let" <+> pretty (rustifyName s) <+> pretty "=" <+> pretty "owl_aead::gen_rand_nonce(CIPHER);"
    NT_Enc _ -> return $ pretty "let" <+> pretty (rustifyName s) <+> pretty "=" <+> pretty "owl_aead::gen_rand_key_iv(CIPHER);"
    NT_MAC _ -> return $ pretty "let" <+> pretty (rustifyName s) <+> pretty "=" <+> pretty "owl_hmac::gen_rand_key(&HMAC_MODE);"
    NT_PKE _ -> return $ pretty "let" <+> (parens . hsep . punctuate comma . map pretty $ [rustifyName s, "pk_" ++ rustifyName s]) <+> pretty "=" <+> pretty "owl_pke::gen_rand_keys();"
    NT_Sig _ -> return $ pretty "let" <+> (parens . hsep . punctuate comma . map pretty $ [rustifyName s, "pk_" ++ rustifyName s]) <+> pretty "=" <+> pretty "owl_pke::gen_rand_keys();"
    NT_DH -> return $ pretty "let" <+> (parens . hsep . punctuate comma . map pretty $ [rustifyName s, "pk_" ++ rustifyName s]) <+> pretty "=" <+> pretty "owl_dhke::gen_ecdh_key_pair();"
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
                case P.parse OwlP.parseFile (takeFileName fn') s of
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
    (locMap, shared, pubkeys) <- foldM (sortName lookupLoc) (locMap, [], []) (mb ^. TB.nameEnv)
    mapM_ sortOrcl $ (mb ^. TB.randomOracle)
    -- TODO random oracles, counters
    return (locMap, shared, pubkeys)
    where
        sortLocs = foldl' (\(locs, locAliases) (locName, locType) -> 
                                case locType of 
                                    Left i -> (M.insert locName i locs, locAliases)
                                    Right p -> (locs, M.insert locName (flattenResolvedPath p) locAliases)) 
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
                locName <- lookupLoc =<< flattenPath locP
                let (args, (_, retTy, body)) = unsafeUnbind (defspec ^. TB.preReq_retTy_body) 
                case body of
                    Nothing -> return m
                    Just e  -> do
                        let f (i, l, s, d, t) = (i, l, s, d ++ [(owlName, loc, sids, args, retTy, e)], t)
                        makeFunc owlName loc sids args retTy
                        return $ M.adjust f locName m
        
        sortTable :: (LocalityName -> ExtractionMonad LocalityName) -> M.Map LocalityName LocalityData -> (String, (Ty, Locality)) -> ExtractionMonad (M.Map LocalityName LocalityData)
        sortTable lookupLoc locMap (name, (ty, Locality locP _)) = do
            locName <- lookupLoc =<< flattenPath locP
            let f (i, l, s, d, t) = (i, l, s, d, t ++ [(name, ty)])
            return $ M.adjust f locName locMap

        sortName :: (LocalityName -> ExtractionMonad LocalityName) 
                    -> (M.Map LocalityName LocalityData, [(NameData, [(LocalityName, Int)])], [NameData]) 
                    -> (String, (Bind ([IdxVar], [IdxVar]) (Maybe (NameType, [Locality]))))
                    -> ExtractionMonad (M.Map LocalityName LocalityData, [(NameData, [(LocalityName, Int)])], [NameData]) 
        sortName lookupLoc (locMap, shared, pubkeys) (name, binds) = do
            let ((sids, pids), ntnlOpt) = unsafeUnbind binds
            case ntnlOpt of
              Nothing -> return (locMap, shared, pubkeys) -- ignore abstract names, they should be concretized when used
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
                locNames <- mapM (\(Locality lname _) -> flattenPath lname) loc
                locNameCounts <- mapM (\(Locality lname lidxs) -> do
                    plname <- flattenPath lname
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

        sortOrcl :: (String, (Bind [IdxVar] ([AExpr], [NameType]))) -> ExtractionMonad ()
        sortOrcl (n, b) = do
            let (_, (args, rtys)) = unsafeUnbind b
            rtlen <- case (map (view val) rtys) of
                [NT_Nonce] -> return "NONCE_SIZE"
                [NT_Enc _] -> return "KEY_SIZE + NONCE_SIZE"
                _ -> throwError $ UnsupportedOracleReturnType n
            oracles %= M.insert n rtlen


-- return number of arguments to main and the print of the locality
extractLoc :: [NameData] -> (LocalityName, LocalityData) -> ExtractionMonad (String, Int, Doc ann)
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
                pretty "#[derive(Serialize, Deserialize, Debug)]" <> pretty "pub struct" <+> pretty (locName loc) <> pretty "_config" <+> braces cfs <> line <>
                pretty "pub struct" <+> pretty (locName loc) <+> braces sfs <> line <>
                pretty "impl" <+> pretty (locName loc) <+> braces (initLoc <+> vsep (indexedNameGetters ++ sharedIndexedNameGetters ++ fns)))
        Nothing -> throwError $ LocalityWithNoMain loc
    where
        genIndexedNameGetter (n, nt, nsids, _) = if nsids == 0 then return $ pretty "" else do
            ni <- nameInit n nt
            return $
                pretty "pub fn get_" <> pretty (rustifyName n) <> tupled (pretty "&mut self" : [pretty "sid" <> pretty n <> pretty ": usize" | n <- [0..(nsids-1)]]) <+> pretty "-> Rc<Vec<u8>>" <> lbrace <> line <>
                    pretty "match self." <> pretty (rustifyName n) <> pretty ".get" <> parens (tupled ([pretty "&sid" <> pretty n | n <- [0..(nsids-1)]])) <> lbrace <> line <>
                        pretty "Some(v) => Rc::clone(v)," <> line <>
                        pretty "None =>" <+> lbrace <> line <>
                            ni <> line <>
                            pretty "let v = Rc::new" <> parens (pretty (rustifyName n)) <> pretty ";" <> line <>
                            pretty "self." <> pretty (rustifyName n) <> pretty ".insert" <> parens (tupled ([pretty "sid" <> pretty n | n <- [0..(nsids-1)]]) <> comma <+> pretty "Rc::clone(&v)") <> pretty ";" <> line <>
                            pretty "Rc::clone(&v)" <> line <>
                        rbrace <>
                    rbrace <>
                rbrace
        genSharedIndexedNameGetter (n, _, nsids, _) = if nsids == 0 then pretty "" else
            pretty "pub fn get_" <> pretty (rustifyName n) <> tupled (pretty "&self" : [pretty "sid" <> pretty n <> pretty ": usize" | n <- [0..(nsids-1)]]) <+> pretty "-> Rc<Vec<u8>>" <> lbrace <> line <>
                pretty "Rc::clone" <> parens (pretty "&self." <> pretty (rustifyName n)) <>
            rbrace

        configFields idxs sharedNames pubKeys =
            vsep . punctuate comma $
                map (\(s,_,_,npids) -> pretty (rustifyName s) <> (if npids == 0 || (idxs == 1 && npids == 1) then pretty ": Vec<u8>" else pretty ": HashMap<usize, Vec<u8>>")) sharedNames ++
                map (\(s,_,_,_) -> pretty "pk_" <> pretty (rustifyName s) <> pretty ": Vec<u8>") pubKeys ++
                [pretty "salt" <> pretty ": Vec<u8>"]
        stateFields idxs localNames sharedNames pubKeys tbls =
            vsep . punctuate comma $
                pretty "listener: TcpListener" :
                map (\(s,_,nsids,npids) -> pretty (rustifyName s) <>
                        if nsids == 0
                        then pretty ": Rc<Vec<u8>>"
                        else pretty ": HashMap" <> angles ((tupled [pretty "usize" | _ <- [0..(nsids - 1)]]) <> comma <+> pretty "Rc<Vec<u8>>")
                    ) localNames ++
                map (\(s,_,_,npids) -> pretty (rustifyName s) <> (if npids == 0 || (idxs == 1 && npids == 1) then pretty ": Rc<Vec<u8>>" else pretty ": Rc<HashMap<usize, Vec<u8>>>")) sharedNames ++
                map (\(s,_,_,_) -> pretty "pk_" <> pretty (rustifyName s) <> pretty ": Rc<Vec<u8>>") pubKeys ++
                -- Tables are always treated as local:
                map (\(n,t) -> pretty (rustifyName n) <> pretty ": HashMap<Vec<u8>, Vec<u8>>") tbls ++
                [pretty "salt" <> pretty ": Rc<Vec<u8>>"]
        genInitLoc loc localNames sharedNames pubKeys tbls = do
            localInits <- mapM (\(s,n,i,_) -> if i == 0 then nameInit s n else return $ pretty "") localNames
            return $ pretty "pub fn init_" <> pretty (locName loc) <+> parens (pretty "config_path : &str") <+> pretty "-> Self" <+> lbrace <> line <>
                pretty "let listener = TcpListener::bind" <> parens (pretty loc <> pretty "_addr") <> pretty ".unwrap();" <>
                vsep localInits <> line <>
                pretty "let config_str = fs::read_to_string(config_path).expect(\"Config file not found\");" <> line <>
                pretty "let config:" <+> pretty (locName loc) <> pretty "_config =" <+> pretty "serde_json::from_str(&config_str).expect(\"Can't parse config file\");" <> line <>
                pretty "return" <+> pretty (locName loc) <+>
                    braces (hsep . punctuate comma $
                        pretty "listener" :
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

extractLocs :: [NameData] ->  M.Map LocalityName LocalityData -> ExtractionMonad (M.Map LocalityName (String, Int), Doc ann)
extractLocs pubkeys locMap = do
    let addrs = mkAddrs 0 $ M.keys locMap
    (sidArgMap, ps) <- foldM (go pubkeys) (M.empty, []) $ M.assocs locMap
    return (sidArgMap, addrs <> line <> vsep ps)
    where
        go pubKeys (m, ps) (lname, ldata) = do
            (mainName, nSidArgs, p) <- extractLoc pubKeys (lname, ldata)
            return (M.insert lname (mainName, nSidArgs) m, ps ++ [p])
        mkAddrs :: Int -> [LocalityName] -> Doc ann
        mkAddrs n [] = pretty ""
        mkAddrs n (l:locs) =
            pretty "pub const" <+> pretty l <> pretty "_addr: &str =" <+> dquotes (pretty "127.0.0.1:" <> pretty (9001 + n)) <> pretty ";" <> line <>
            mkAddrs (n+1) locs

entryPoint :: M.Map LocalityName LocalityData -> [(NameData, [(LocalityName, Int)])] -> [NameData] -> M.Map LocalityName (String, Int) -> ExtractionMonad (Doc ann)
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
                                        Just (m, n) -> return (l, m, n)
                                        Nothing -> throwError $ ErrSomethingFailed $ "couldn't look up number of sessionID args for " ++ l ++ ", bug in extraction"
                            ) allLocs
    let runLocs = map genRunLoc allLocsSidArgs
    return $ pretty "fn main()" <+> lbrace <> line <>
        pretty "let args: Vec<String> = env::args().collect();" <> line <>
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
                    (map (\(n,_,_,_) -> pretty (rustifyName n) <+> pretty ":" <+> pretty (rustifyName n) <> (if npids == 0 then pretty "" else pretty ".get(&i).unwrap()") <> pretty ".clone()") ss ++
                     map (\n -> pretty "pk_" <> pretty (rustifyName n) <+> pretty ":" <+> pretty "pk_" <> pretty (rustifyName n) <> pretty ".clone()") pubKeys ++
                     [pretty "salt" <+> pretty ":" <+> pretty "salt" <> pretty ".clone()"]) in
            (if npids == 0 then pretty "" else pretty "for i in 0..n_" <> pretty (locName loc) <+> lbrace) <>
            pretty "let" <+> pretty (locName loc) <> pretty "_config" <+> pretty "=" <+> pretty (locName loc) <> pretty "_config" <+> braces configInits <> pretty ";" <> line <>
            pretty "let" <+> pretty (locName loc) <> pretty "_config_serialized" <+> pretty "=" <+>
                    pretty "serde_json::to_string" <> parens (pretty "&" <> pretty (locName loc) <> pretty "_config") <> pretty ".unwrap();" <> line <>
            pretty "let mut" <+> pretty (locName loc) <> pretty "_f" <+> pretty "=" <+>
                pretty "fs::File::create(format!(\"{}/{}" <> (if npids == 0 then pretty "" else pretty "_{}") <> pretty ".owl_config\", &args[2]," <+>
                    dquotes (pretty (locName loc)) <> (if npids == 0 then pretty "" else pretty ",i") <> pretty ")).expect(\"Can't create config file\");" <> line <>
            pretty (locName loc) <> pretty "_f" <> pretty ".write_all" <> parens (pretty (locName loc) <> pretty "_config_serialized.as_bytes()")
                                <> pretty ".expect(\"Can't write config file\");" <>
            (if npids == 0 then pretty "" else rbrace)

        genRunLoc (loc, mainName, nSidArgs) =
            let body = genRunLocBody loc mainName nSidArgs in
            pretty "if" <+> (hsep . punctuate (pretty " && ") . map pretty $ ["args.len() >= 4", "args[1] == \"run\"", "args[2] == \"" ++ loc ++ "\""]) <>
                braces body <> pretty "else"
        genRunLocBody loc mainName nSidArgs =
            pretty "let mut s =" <+> pretty (locName loc) <> pretty "::init_" <> pretty (locName loc) <>
                parens (pretty "&args[3]") <> pretty ";" <> line <>
            pretty "println!(\"Waiting for 5 seconds to let other parties start...\");" <> line <>
            pretty "thread::sleep(Duration::new(5, 0));" <> line <>
            pretty "println!(\"Running" <+> pretty mainName <+> pretty "...\");" <> line <>
            pretty "let now = Instant::now();" <> line <>
            pretty "let res = s." <> pretty mainName <> tupled [pretty i | i <- [1..nSidArgs]] <> pretty ";" <> line <>
            pretty "let elapsed = now.elapsed();" <> line <>
            pretty "println!" <> parens (dquotes (pretty loc <+> pretty "returned {:?}") <> pretty "," <+> pretty "res") <> pretty ";" <> line <>
            pretty "println!" <> parens (dquotes (pretty "Elapsed: {:?}") <> pretty "," <+> pretty "elapsed") <> pretty ";"


-------------------------------------------------------------------------------------------
--- Entry point of extraction


extractTyDefs :: [(TyVar, TB.TyDef)] -> ExtractionMonad (Doc ann)
extractTyDefs [] = return $ pretty ""
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
            return $ pretty ""
        extractTyDef name TB.TyAbstract = do
            typeLayouts %= M.insert (rustifyName name) (LBytes 0) -- Replaced later when instantiated
            return $ pretty ""

preamble :: ExtractionMonad (Doc ann)        
preamble = do
    c <- showAEADCipher
    h <- showHMACMode
    return $ vsep $ map pretty
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
            pretty ""
        ]
    where
        owlOpsTraitDef = vsep $ map pretty [
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
        owlOpsTraitImpls = vsep $ map pretty [
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
        owl_msgDef = vsep $ map pretty [
                "#[derive(Serialize, Deserialize, Debug)]",
                "pub struct msg {",
                    "ret_addr: String,",
                    "payload: Vec<u8>",
                "}"
            ]
        owl_outputDef = vsep $ map pretty [
                "pub fn output<A: ToSocketAddrs>(x: &[u8], dest_addr: &A, ret_addr: &str) {",
                    "let msg = msg { ret_addr: String::from(ret_addr), payload: Vec::from(x) };",
                    "let serialized = serde_json::to_vec(&msg).unwrap();",
                    "let mut stream = TcpStream::connect(dest_addr).unwrap();",
                    "stream.write_all(&serialized).unwrap();",
                    "stream.flush().unwrap();",
                "}"
            ]
        owl_inputDef = vsep $ map pretty [
                "pub fn owl_input(listener: &TcpListener) -> (Vec<u8>, String) {",
                    "let (mut stream, _addr) = listener.accept().unwrap();",
                    "let mut reader = io::BufReader::new(&mut stream);",
                    "let received: Vec<u8> = reader.fill_buf().unwrap().to_vec();",
                    "reader.consume(received.len());",
                    "let msg : msg = serde_json::from_slice(&received).expect(\"Couldn't parse input\");",
                    "(msg.payload, msg.ret_addr)",
                "}"
            ]
        owl_miscFns = vsep $ map pretty [
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




extractModBody :: TB.ModBody -> ExtractionMonad (Doc ann) 
extractModBody mb = do
    (locMap, sharedNames, pubKeys) <- preprocessModBody mb
    -- We get the list of tyDefs in reverse order of declaration, so reverse again
    tyDefsExtracted <- extractTyDefs $ reverse (mb ^. TB.tyDefs)
    (sidArgMap, locsExtracted) <- extractLocs pubKeys locMap
    p <- preamble
    ep <- entryPoint locMap sharedNames pubKeys sidArgMap
    return $ p <> line <> tyDefsExtracted <> line <> locsExtracted <> line <> ep

extract :: TB.Env -> String -> TB.ModBody -> IO (Either ExtractionError (Doc ann))
extract tcEnv path modbody = runExtractionMonad tcEnv (initEnv path (modbody ^. TB.userFuncs)) $ extractModBody modbody
