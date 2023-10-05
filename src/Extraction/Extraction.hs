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

extractStruct :: String -> [(String, Ty)] -> ExtractionMonad (OwlDoc, OwlDoc)
extractStruct owlName owlFields = do
    let name = rustifyName owlName
    -- liftIO $ print name
    let parsingOutcomeName = name ++ "_ParsingOutcome"
    let typeDef = owlpretty "pub struct" <+> owlpretty name <+> owlpretty "{ pub data: Rc<Vec<u8>>, pub parsing_outcome: " <+> owlpretty parsingOutcomeName <> owlpretty "}"
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
    adtFuncs %= M.union structFuncs
    typeLayouts %= M.insert name layout
    structSpec <- Spec.extractStruct owlName owlFields
    return $ (vsep $ [typeDef, parsingOutcomeDef, lenValidFnDef, parseFnDef, constructorDef] ++ selectorDefs, structSpec)
    where
        mkStructFuncs owlName parsingOutcomeName owlFields = return $
            M.fromList $
                -- don't need to check arity
                (owlName, (rustifyName owlName, ADT (rustifyName owlName), False, \args -> return $ show $
                        owlpretty "construct_" <> (owlpretty . rustifyName) owlName <>
                            (parens . hsep . punctuate comma . map (\(t,a) -> owlpretty "&" <> (case t of
                                ADT _ -> parens (owlpretty "*" <> owlpretty a <> owlpretty ".data") <> owlpretty ".as_slice()"
                                RcVecU8 -> parens (owlpretty "*" <> owlpretty a) <> owlpretty ".as_slice()"
                                VecU8 -> owlpretty a <> owlpretty ".as_slice()"
                                _ -> owlpretty a))
                            $ args
                        ))) :
                map (\(owlField, _) -> (owlField, (rustifyName owlName, RcVecU8, True, \args -> do
                    case args of
                      (ADT _, arg) : _ -> do
                        return $ show $
                            owlpretty "rc_new(slice_to_vec(get_" <> (owlpretty . rustifyName) owlField <> owlpretty "_" <> (owlpretty . rustifyName) owlName <> 
                                parens (owlpretty "&mut" <+> owlpretty arg) <> owlpretty "))"
                      (VecU8, arg) : _ -> do
                        return $ show $
                            owlpretty "rc_new(slice_to_vec(get_" <> (owlpretty . rustifyName) owlField <> owlpretty "_" <> (owlpretty . rustifyName) owlName <>
                                parens (owlpretty "&mut" <+> owlpretty arg) <> owlpretty "))"
                      (RcVecU8, arg) : _ -> do
                        return $ show $
                            owlpretty "rc_new(slice_to_vec(get_" <> (owlpretty . rustifyName) owlField <> owlpretty "_" <> (owlpretty . rustifyName) owlName <>
                                parens (owlpretty "&mut" <+> owlpretty arg) <> owlpretty "))"
                      _ -> throwError $ TypeError $ "attempt to get from " ++ owlName ++ " with bad args"
                ))) owlFields

        genStructParsingOutcomeDef parsingOutcomeName layoutFields = return $
            owlpretty "// #[derive(PartialEq, Eq, Debug)]" <> line <>
            -- owlpretty "#[is_variant] #[derive(Clone)]" <> line <>
            owlpretty "pub enum" <+> owlpretty parsingOutcomeName <+>
            vsep [  lbrace,
                    owlpretty "Success" <> parens (hsep $ punctuate comma $ replicate (length layoutFields + 1) $ owlpretty "usize") <> comma,
                    owlpretty "Failure" <> comma,
                    rbrace]

        genLenValidFnDef name layoutFields =
            let fieldCheckers = map fieldChecker layoutFields in
            let startsPrettied = hsep $ punctuate comma (map (\(n,_) -> owlpretty "start_" <> owlpretty n) layoutFields ++ [owlpretty "i"]) in
            return $ owlpretty "#[verifier(external_body)] pub fn" <+> owlpretty "len_valid_" <> owlpretty name <> parens (owlpretty "arg: &[u8]") <+>
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
                owlpretty "i = i + " <+> owlpretty nb <> owlpretty ";"
            LStruct sn sfs ->
                owlpretty "let start_" <> owlpretty n <+> owlpretty "= i;" <> line <>
                owlpretty "match" <+> owlpretty "len_valid_" <> owlpretty sn <> parens (owlpretty "&arg[i..]") <+> lbrace <> line <>
                owlpretty "Some" <> (parens . parens . hsep . punctuate comma $ [owlpretty "_" | _ <- [0..(length sfs - 1)]] ++ [owlpretty "l"]) <+> owlpretty "=>" <+> braces (owlpretty "i = i + l;") <> line <>
                owlpretty "None => " <> braces (owlpretty "return None;") <> line <>
                rbrace
            LEnum en _   ->
                owlpretty "let start_" <> owlpretty n <+> owlpretty "= i;" <> line <>
                owlpretty "match" <+> owlpretty "len_valid_" <> owlpretty en <> parens (owlpretty "&arg[i..]") <+> lbrace <> line <>
                owlpretty "Some(l) => " <> braces (owlpretty "i = i + l;") <> line <>
                owlpretty "None => " <> braces (owlpretty "return None;") <> line <>
                rbrace

        genParseFnDef name parsingOutcomeName layout layoutFields = return $
            owlpretty "#[verifier(external_body)] pub fn" <+> owlpretty "parse_into_" <> owlpretty name <> parens (owlpretty "arg: &mut" <+> owlpretty name) <+> line <> 
            owlpretty "ensures" <+>
                -- TODO improve
                owlpretty "parse_" <> owlpretty (specName . unrustifyName $ name) <> owlpretty "(arg.data@).is_Some() ==> arg.data@ === old(arg).data@" <> comma <> line <>
                owlpretty "parse_" <> owlpretty (specName . unrustifyName $ name) <> owlpretty "(arg.data@).is_None() ==> arg.data@ === seq![] // TODO" <> comma <> line <>
            lbrace <> line <>
                owlpretty "match arg.parsing_outcome" <+> lbrace <> line <> 
                    owlpretty parsingOutcomeName <> owlpretty "::Failure =>" <+> lbrace <> line <>
                        owlpretty "match len_valid_" <> owlpretty name <> parens (owlpretty "&(*arg.data).as_slice()") <+> lbrace <> line <>
                        owlpretty "Some" <> (parens . parens . hsep . punctuate comma $ [owlpretty "idx_" <> owlpretty j | j <- [0..(length layoutFields)]]) <+>
                            owlpretty "=>" <+> braces (
                                owlpretty "arg.parsing_outcome =" <+> owlpretty parsingOutcomeName <> owlpretty "::Success" <>
                                    (parens . hsep . punctuate comma $ [owlpretty "idx_" <> owlpretty j | j <- [0..(length layoutFields)]]) <>
                                owlpretty ";"
                            ) <> line <>
                        owlpretty "None => " <> braces (
                                owlpretty "arg.data =" <+> owlpretty "rc_new(vec_u8_from_elem(0," <+> owlpretty (lenLayoutFailure layout) <> owlpretty "));" <> line <>
                                owlpretty "arg.parsing_outcome =" <+> owlpretty parsingOutcomeName <> owlpretty "::Failure;"
                            ) <> line <>
                        rbrace <> line <>
                    rbrace <> comma <> line <>
                    owlpretty "_ => {}" <>
                rbrace <> line <>
            rbrace


        genConstructorDef name parsingOutcomeName layout layoutFields = do
            let argsPrettied = hsep $ punctuate comma $ map (\(n,_) -> owlpretty "arg_" <> owlpretty n <> owlpretty ": &[u8]") layoutFields
            let viewArgsPrettied = hsep $ punctuate comma $ map (\(n,_) -> owlpretty "arg_" <> owlpretty n <> owlpretty "@") layoutFields
            let startsPrettied = hsep $ punctuate comma (map (\(n,_) -> owlpretty "start_" <> owlpretty n) layoutFields ++ [owlpretty "i"])
            let checkAndExtenders = map (\(n,l) -> checkAndExtender name (lenLayoutFailure layout) parsingOutcomeName n l) layoutFields
            return $ 
                owlpretty "#[verifier(external_body)] pub fn" <+> owlpretty "construct_" <> owlpretty name <> parens argsPrettied <+> owlpretty "->" <+> parens (owlpretty "res:" <+> owlpretty name) <+> line <>
                owlpretty "ensures res.data@ ===" <+> owlpretty owlName <> parens viewArgsPrettied <> line <>
                lbrace <> line <>
                    owlpretty "let mut v = vec_u8_from_elem(0,0);" <> line <>
                    owlpretty "let mut i = 0;" <> line <>
                    vsep checkAndExtenders <> line <>
                    owlpretty "let res =" <+> owlpretty name <+> owlpretty "{ data: rc_new(v), parsing_outcome:" <+> owlpretty parsingOutcomeName <> owlpretty "::Success" <> parens startsPrettied <> owlpretty "};" <> line <>
                    owlpretty "res" <> line <>
                rbrace
        checkAndExtender name lenFailure parsingOutcomeName n l =
            let structEnumChecker dn = owlpretty "len_valid_" <> owlpretty dn <> parens (owlpretty "arg_" <> owlpretty n) <+> owlpretty " == None" in
            let checker = case l of
                    LBytes i     -> owlpretty "arg_" <> owlpretty n <> owlpretty ".len()" <+> owlpretty "!=" <+> owlpretty i
                    LStruct sn _ -> structEnumChecker sn
                    LEnum en _   -> structEnumChecker en in
            owlpretty "let start_" <> owlpretty n <+> owlpretty "= i;" <> line <>
            owlpretty "if" <+> checker <+> lbrace <> line <>
            owlpretty "return" <+> owlpretty name <+> braces (owlpretty "data: rc_new(vec_u8_from_elem(0," <+> owlpretty lenFailure <> owlpretty ")), parsing_outcome:" <+> owlpretty parsingOutcomeName <> owlpretty "::Failure") <> owlpretty ";" <> line <>
            rbrace <> line <>
            owlpretty "v.extend" <> parens (owlpretty "arg_" <> owlpretty n) <> owlpretty ";" <> line <>
            owlpretty "i = i + " <> owlpretty "arg_" <> owlpretty n <> owlpretty ".len();"

        genSelectorDefs name parsingOutcomeName layoutFields = do
            let (_, layoutOffsets) = mapAccumL (\(o,i) (n,l) -> let nextO = o + lenLayoutFailure l in ((nextO, i + 1), (n,l,o,nextO,i))) (0,0) layoutFields
            return $ map (genSelectorDef name parsingOutcomeName (length layoutFields)) layoutOffsets

        genSelectorDef :: String -> String -> Int -> (String, Layout, Int, Int, Int) -> OwlDoc
        genSelectorDef name parsingOutcomeName numFields (fieldName, fieldLayout, failOffset, failNextOffset, structIdx) =
            let success_pattern = owlpretty parsingOutcomeName <> owlpretty "::Success" <> (parens . hsep . punctuate comma $ [owlpretty "idx_" <> owlpretty j | j <- [0..numFields]]) in
            -- return $
            owlpretty "#[verifier(external_body)] pub fn" <+> owlpretty "get_" <> owlpretty fieldName <> owlpretty "_" <> owlpretty name <> parens (owlpretty "arg: &mut" <+> owlpretty name) <+> owlpretty "->" <+> owlpretty "(res: &[u8])" <+> line <>
            -- TODO make this better
            owlpretty "ensures res@ ===" <+> owlpretty (unrustifyName fieldName) <> parens (owlpretty "old(arg).data@") <> line <>
            lbrace <> line <>
            owlpretty "// parse_into_" <> owlpretty name <> parens (owlpretty "arg") <> owlpretty ";" <> line <>
            owlpretty "match arg.parsing_outcome {" <> line <>
            success_pattern <+> owlpretty "=>" <+>
                owlpretty "slice_subrange(&(*arg.data).as_slice(), idx_" <> owlpretty structIdx <> owlpretty ", idx_" <> owlpretty (structIdx + 1) <> owlpretty ")," <> line <>
            owlpretty parsingOutcomeName <> owlpretty "::Failure => slice_subrange(&(*arg.data).as_slice()," <+> owlpretty failOffset <> owlpretty "," <+> owlpretty failNextOffset <> owlpretty ")" <> line <>
            owlpretty "}" <> line <>
            owlpretty "}"



extractEnum :: String -> [(String, Maybe Ty)] -> ExtractionMonad (OwlDoc, OwlDoc)
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
    let typeDef = tagsComment <> line <> owlpretty "pub struct" <+> owlpretty name <+> owlpretty "{ pub data: Rc<Vec<u8>>, pub parsing_outcome: " <+> owlpretty parsingOutcomeName <> owlpretty "}"    
    parsingOutcomeDef <- genEnumParsingOutcomeDef parsingOutcomeName
    lenValidFnDef <- genLenValidFnDef name layoutCases
    parseFnDef <- genParseFnDef name parsingOutcomeName layout
    constructorDefs <- genConstructorDefs name parsingOutcomeName layout layoutCases
    enumFuncs <- mkEnumFuncs owlName owlCases
    adtFuncs %= M.union enumFuncs
    typeLayouts %= M.insert name layout
    enums %= M.insert (S.fromList (map fst owlCases')) owlName
    enumSpec <- Spec.extractEnum owlName owlCases'
    return $ (vsep $ [typeDef, parsingOutcomeDef, lenValidFnDef, parseFnDef] ++ constructorDefs, enumSpec)
    where
        mkEnumFuncs owlName owlCases = return $
            M.fromList $
                map (\(owlCase, _) -> (owlCase, (rustifyName owlName, ADT (rustifyName owlName), False, \args -> return $ show $
                    owlpretty "construct_" <> (owlpretty . rustifyName) owlName <> owlpretty "_" <> (owlpretty . rustifyName) owlCase <>
                        (parens . hsep . punctuate comma . map (\(t,a) -> owlpretty "&" <> (case t of
                                ADT _ -> parens (owlpretty "*" <> owlpretty a <> owlpretty ".data") <> owlpretty ".as_slice()"
                                RcVecU8 -> parens (owlpretty "*" <> owlpretty a) <> owlpretty ".as_slice()"
                                VecU8 -> owlpretty a <> owlpretty ".as_slice()"
                                _ -> owlpretty a)) $ args
                )))) $ M.assocs owlCases

        genEnumParsingOutcomeDef parsingOutcomeName = return $
            owlpretty "// #[derive(PartialEq, Eq, Debug)]" <> line <>
            -- owlpretty "#[is_variant] #[derive(Clone)]" <> line <>
            owlpretty "pub enum" <+> owlpretty parsingOutcomeName <+>
            vsep [  lbrace,
                    owlpretty "Success" <> comma,
                    owlpretty "Failure" <> comma,
                    rbrace]

        genLenValidFnDef name layoutCases =
            let caseCheckers = map caseChecker $ M.assocs layoutCases in
            return $ owlpretty "#[verifier(external_body)] pub fn" <+> owlpretty "len_valid_" <> owlpretty name <> parens (owlpretty "arg: &[u8]") <+>
                owlpretty " -> Option<usize>" <+> lbrace <> line <>
            owlpretty "if arg.len() < 1 { return None; } else " <> line <>
            vsep (punctuate (owlpretty " else ") caseCheckers) <> line <>
            owlpretty "else { return None; }" <> line <>
            rbrace
        caseChecker (t, (n, l)) = case l of
            Just (LBytes nb)      ->
                owlpretty "if *slice_index_get(arg, 0) ==" <+> owlpretty n <> owlpretty "u8" <+> owlpretty "&&" <+> owlpretty "arg.len() >=" <+> owlpretty (1 + nb) <+>
                braces (owlpretty " return Some(" <+> owlpretty (1 + nb) <> owlpretty "); ")
            Just (LStruct sn sfs) ->
                owlpretty "if *slice_index_get(arg, 0) ==" <+> owlpretty n <> owlpretty "u8" <+> braces (
                    owlpretty "match" <+> owlpretty "len_valid_" <> owlpretty sn <> parens (owlpretty "&arg[1..]") <+> lbrace <> line <>
                    owlpretty "Some" <> (parens . parens . hsep . punctuate comma $ [owlpretty "_" | _ <- [0..(length sfs - 1)]] ++ [owlpretty "l"]) <+>
                        owlpretty "=>" <+> braces (owlpretty "return Some(1 + l);") <> line <>
                    owlpretty "None => " <> braces (owlpretty "return None;") <> line <>
                    rbrace
                )
            Just (LEnum en _)     ->
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
            owlpretty "#[verifier(external_body)] pub fn" <+> owlpretty "parse_into_" <> owlpretty name <> parens (owlpretty "arg: &mut" <+> owlpretty name) <+> lbrace <> line <>
                owlpretty "match arg.parsing_outcome" <+> lbrace <> line <> 
                    owlpretty parsingOutcomeName <> owlpretty "::Failure =>" <+> lbrace <> line <>
                        owlpretty "match len_valid_" <> owlpretty name <> parens (owlpretty "&(*arg.data).as_slice()") <+> lbrace <> line <>
                            owlpretty "Some(l)" <+>
                                owlpretty "=>" <+> braces (owlpretty "arg.parsing_outcome =" <+> owlpretty parsingOutcomeName <> owlpretty "::Success;") <> line <>
                            owlpretty "None => " <> braces (
                                    owlpretty "arg.data =" <+> owlpretty "rc_new(vec_u8_from_elem(0," <+> owlpretty (lenLayoutFailure layout) <> owlpretty "));" <> line <>
                                    owlpretty "arg.parsing_outcome =" <+> owlpretty parsingOutcomeName <> owlpretty "::Failure;"
                                ) <> line <>
                        rbrace <> line <>
                    rbrace <> comma <> line <>
                    owlpretty "_ => {}" <>
                rbrace <> line <>
            rbrace

        genConstructorDefs name parsingOutcomeName layout layoutCases =
            return $ map (genConstructorDef name parsingOutcomeName) $ M.assocs layoutCases

        genConstructorDef :: String -> String -> (String, (Int, Maybe Layout)) -> OwlDoc
        genConstructorDef name parsingOutcomeName (tagName, (tag, Just (LBytes 0))) = -- special case for a case with no payload, where the constructor takes no arg
            owlpretty "#[verifier(external_body)] pub fn" <+> owlpretty "construct_" <> owlpretty name <> owlpretty "_" <> owlpretty tagName <> owlpretty "()" <+> owlpretty "->" <+> parens (owlpretty "res:" <+> owlpretty name) <+> line <> 
            -- TODO improve
            owlpretty "ensures" <+> owlpretty "res.data.view() ===" <+> owlpretty (unrustifyName tagName) <> owlpretty "()" <> line <>
            lbrace <> line <>
                owlpretty "let v = vec_u8_from_elem(" <> owlpretty tag <> owlpretty "u8, 1);" <> line <>
                owlpretty "let res =" <+> owlpretty name <+> owlpretty "{ data: rc_new(v), parsing_outcome: " <+> owlpretty parsingOutcomeName <> owlpretty "::Success" <> owlpretty "};" <> line <>                owlpretty "res" <> line <>
            rbrace

        genConstructorDef name parsingOutcomeName (tagName, (tag, tagLayout)) =
            -- Failure case for struct is always a zero tag with no payload
            let failureReturn = owlpretty "return" <+> owlpretty name <+> braces (owlpretty "data: rc_new(vec_u8_from_elem(0, 1)), parsing_outcome: " <+> owlpretty parsingOutcomeName <> owlpretty "::Failure") <> owlpretty ";" in
            let checkAndExtender = case tagLayout of
                    Just (LBytes nb)    ->
                        owlpretty "if" <+> owlpretty "arg.len()" <+> owlpretty "<" <+> owlpretty nb <+> braces failureReturn <> line <>
                        owlpretty "extend_vec_u8" <> parens (owlpretty "&mut v," <+> owlpretty "slice_subrange(arg, 0, " <> owlpretty nb <> owlpretty ")") <> owlpretty ";" <> line
                    Just (LStruct sn sfs) ->
                        owlpretty "match" <+> owlpretty "len_valid_" <> owlpretty sn <> parens (owlpretty "arg") <+> lbrace <> line <>
                        owlpretty "Some" <> (parens . parens . hsep . punctuate comma $ [owlpretty "_" | _ <- [0..(length sfs - 1)]] ++ [owlpretty "l"]) <+>
                            owlpretty "=>" <+> braces (owlpretty "extend_vec_u8" <> parens (owlpretty "&mut v," <+> owlpretty "slice_subrange(arg, 0, l)") <> owlpretty ";") <> line <>
                        owlpretty "None => " <> braces failureReturn <> line <>
                        rbrace
                    Just (LEnum en _)   ->
                        owlpretty "match" <+> owlpretty "len_valid_" <> owlpretty en <> parens (owlpretty "arg") <+> lbrace <> line <>
                        owlpretty "Some(l) => " <> braces (owlpretty "extend_vec_u8" <> parens (owlpretty "&mut v," <+> owlpretty "slice_subrange(arg, 0, l)") <> owlpretty ";") <> line <>
                        owlpretty "None => " <> braces failureReturn <> line <>
                        rbrace
                    Nothing ->
                        owlpretty "extend_vec_u8(&mut v, arg);"
                in
            owlpretty "#[verifier(external_body)] pub fn" <+> owlpretty "construct_" <> owlpretty name <> owlpretty "_" <> owlpretty tagName <> parens (owlpretty "arg: &[u8]") <+> owlpretty "->" <+> parens (owlpretty "res:" <+> owlpretty name) <+> line <>
            owlpretty "ensures" <+> owlpretty "res.data.view() ===" <+> owlpretty (unrustifyName tagName) <> parens (owlpretty "arg@") <> line <>
            lbrace <> line <>
                owlpretty "let mut v = vec_u8_from_elem(" <> owlpretty tag <> owlpretty "u8, 1);" <> line <>
                checkAndExtender <> line <>
                owlpretty "let res =" <+> owlpretty name <+> owlpretty "{data: rc_new(v), parsing_outcome: " <+> owlpretty parsingOutcomeName <> owlpretty "::Success" <> owlpretty "};" <> line <>
                owlpretty "res" <> line <>
            rbrace

-------------------------------------------------------------------------------------------
-- Code generation

extractCryptOp :: M.Map String (RustTy, Maybe AExpr) -> CryptOp -> [AExpr] -> ExtractionMonad (RustTy, OwlDoc, OwlDoc)
extractCryptOp binds op owlArgs = do
    argsPretties <- mapM (extractAExpr binds . view val) owlArgs
    let preArgs = foldl (\p (_,s,_) -> p <> s) (owlpretty "") argsPretties
    let args = map (\(r, _, p) -> (r, show p)) argsPretties
    (rt, preCryptOp, str) <- case (op, args) of
        (CHash ((ropath,_,_):_) i, [x]) -> do 
            -- Typechecking checks that the list of hints is non-empty and that all hints point to consistent return type name kinds,
            -- so we can just use the first one to calculate the length to extract to
            roname <- flattenPath ropath
            orcls <- use oracles
            (outLen, sliceIdxs) <- case orcls M.!? roname of
                Nothing -> throwError $ TypeError $ "unrecognized random oracle " ++ roname
                Just (outLen', sliceIdxs) -> do
                    outLen'' <- mapM printLenConst outLen'
                    return (intercalate "+" outLen'', sliceIdxs)
            (start, end) <- case sliceIdxs M.!? i of
                Nothing -> throwError $ TypeError $ "bad index " ++ show i ++ " to random oracle " ++ roname
                Just (s', e') -> do
                    s'' <- mapM printLenConst s'
                    e'' <- mapM printLenConst e'
                    return (intercalate "+" s'', intercalate "+" e'')
            -- Check if we have already evaluated this RO; if not, evaluate it
            resolvedArgs <- mapM (resolveANF binds) owlArgs
            oopt <- lookupHashCall (roname, resolvedArgs)
            (genOrcl, orclName) <- case oopt of
                Just (RcVecU8, name) -> return (pretty "", name)
                Nothing -> do
                    rovar' <- fresh . s2n $ roname
                    let rovar = rustifyName . show $ rovar'
                    hashCalls %= (:) ((roname, resolvedArgs), (RcVecU8, rovar))
                    let genOrcl = 
                            owlpretty "let" <+> owlpretty rovar <+> owlpretty "=" <+>
                            owlpretty (printOwlOp "owl_extract_expand_to_len" [(RcVecU8, "self.salt"), (Number, outLen), x]) <> owlpretty ";"
                    return (genOrcl, rovar)
                _ -> throwError $ ErrSomethingFailed "precomputed hash value has wrong type"
            let sliceOrcl = owlpretty "rc_new" <> parens (
                                owlpretty "slice_to_vec" <> parens (
                                    owlpretty "slice_subrange" <> parens (
                                        parens (owlpretty "*" <> owlpretty orclName) <> owlpretty ".as_slice()" <> comma <+>
                                        owlpretty start <> comma <+> owlpretty end
                                    )
                                )
                            )
            return (RcVecU8, genOrcl, sliceOrcl)
        (CPRF s, _) -> do throwError $ ErrSomethingFailed $ "TODO implement crypto op: " ++ show op
        (CAEnc, [k, x]) -> do 
            typeAnnot <- do
                t <- getCurRetTy
                return $ owlpretty "::" <> angles (owlpretty t)
            let genSample = owlpretty "let coins = owl_sample" <> typeAnnot <> owlpretty "(Tracked(&mut itree), nonce_size());"
            let encOp = owlpretty $ printOwlOp "owl_enc" [k, x, (VecU8, "coins")]
            return (RcVecU8, owlpretty "", genSample <+> encOp)
        (CADec, [k, x]) -> do return (Option RcVecU8, owlpretty "", owlpretty $ printOwlOp "owl_dec" [k, x])
        (CEncStAEAD np _, [k, x, aad]) -> do 
            n <- flattenPath np
            let encOp = owlpretty $ printOwlOp "owl_enc_st_aead" [k, x, (Number, "&mut mut_state." ++ rustifyName n), aad]
            let unwrapped = 
                    owlpretty "match" <+> encOp <+> braces (
                        owlpretty "Ok(ctxt) => ctxt," <> line <>
                        owlpretty "Err(e) => { return Err(e) },"
                    )
            return (RcVecU8, owlpretty "", unwrapped)
        (CDecStAEAD, [k, c, aad, n]) -> do return (Option RcVecU8, owlpretty "", owlpretty $ printOwlOp "owl_dec_st_aead" [k, c, n, aad])
        (CPKEnc, [k, x]) -> do return (RcVecU8, owlpretty "", owlpretty $ printOwlOp "owl_pkenc" [k, x])
        (CPKDec, [k, x]) -> do return (RcVecU8, owlpretty "", owlpretty $ printOwlOp "owl_pkdec" [k, x])
        (CMac, [k, x]) -> do return (RcVecU8, owlpretty "", owlpretty $ printOwlOp "owl_mac" [k, x])
        (CMacVrfy, [k, x, v]) -> do return (Option RcVecU8, owlpretty "", owlpretty $ printOwlOp "owl_mac_vrfy" [k, x, v])
        (CSign, [k, x]) -> do return (RcVecU8, owlpretty "", owlpretty $ printOwlOp "owl_sign" [k, x])
        (CSigVrfy, [k, x, v]) -> do return (Option RcVecU8, owlpretty "", owlpretty $ printOwlOp "owl_vrfy" [k, x, v])
        (_, _) -> do throwError $ TypeError $ "got bad args for crypto op: " ++ show op ++ "(" ++ show args ++ ")"
    return (rt, preArgs <> line <> preCryptOp, str)
    where 
        printLenConst "0" = return "0"
        printLenConst "nonce" = return "nonce_size()"
        printLenConst "enckey" = return "key_size()"
        printLenConst s = throwError $ UndefinedSymbol $ "unrecognized oracle length const: " ++ s


extractAExpr :: M.Map String (RustTy, Maybe AExpr) -> AExprX -> ExtractionMonad (RustTy, OwlDoc, OwlDoc)
extractAExpr binds (AEVar _ owlV) = do
    let v = rustifyName . show $ owlV
    case binds M.!? v of
      Nothing -> do
        debugPrint $ "failed to find " ++ show v ++ " in binds: " ++ show binds
        return (VecU8, owlpretty "", owlpretty v)
      Just (RcVecU8, _) -> return (RcVecU8, owlpretty "", rcClone <> parens (owlpretty "&" <> owlpretty v))
      -- Just (ADT t) -> 
      Just (rt, _) -> return (rt, owlpretty "", owlpretty v)
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
            adtf <- lookupAdtFunc =<< flattenPath owlFn
            case adtf of
                Just (adt, rt, needsParse, f) -> do
                    if needsParse && length args == 1 then do
                        -- We are in a case requiring parsing. Check if we have already parsed 
                        resolvedArgs <- mapM (resolveANF binds) owlArgs
                        debugPrint $ owlpretty adt <> tupled (map owlpretty resolvedArgs)
                        oopt <- lookupAdtCall (adt, resolvedArgs)
                        (doParse, str) <- case oopt of
                            Just arg -> do
                                str <- f [arg]
                                return (pretty "", str) 
                            Nothing -> do
                                p <- flattenPath owlFn
                                var' <- fresh . s2n $ adt ++ "_" ++ p
                                let var = rustifyName . show $ var'
                                adtCalls %= (:) ((adt, resolvedArgs), (ADT adt, var))
                                let doParse = 
                                        owlpretty "let mut" <+> owlpretty var <+> owlpretty "=" <+> owlpretty adt <+> braces (owlpretty "data:" <+> owlpretty (map snd args) <> comma <+> owlpretty "parsing_outcome:" <+> owlpretty adt <> owlpretty "_ParsingOutcome::Failure") <> owlpretty ";" <> line <>
                                        owlpretty "parse_into_" <> owlpretty adt <> parens (owlpretty "&mut" <+> owlpretty var) <> owlpretty ";"
                                str <- f [(ADT adt, var)]
                                return (doParse, str)
                        return (rt, preArgs <> doParse, owlpretty str)
                    else do
                        str <- f args
                        return (rt, preArgs, owlpretty str)
                Nothing ->
                    throwError $ UndefinedSymbol $ show owlFn
extractAExpr binds (AEHex s) = do
    bytelist <- hexStringToByteList s
    return (VecU8, owlpretty "", owlpretty "vec![" <> bytelist <> owlpretty "]")
extractAExpr binds (AEInt n) = return (Number, owlpretty "", owlpretty n)
extractAExpr binds (AEGet nameExp) = do
    fnameExp <- flattenNameExp nameExp
    return (RcVecU8, owlpretty "", rcClone <> parens (owlpretty "&self." <> owlpretty fnameExp))
extractAExpr binds (AEGetEncPK nameExp) = do
    fnameExp <- flattenNameExp nameExp
    return (RcVecU8, owlpretty "", rcClone <> parens (owlpretty "&self.pk_" <> owlpretty fnameExp))
extractAExpr binds (AEGetVK nameExp) = do
    fnameExp <- flattenNameExp nameExp
    return (RcVecU8, owlpretty "", rcClone <> parens (owlpretty "&self.pk_" <> owlpretty fnameExp))
extractAExpr binds (AEPackIdx idx ae) = extractAExpr binds (ae^.val)
extractAExpr binds (AELenConst s) = do
    lcs <- use lenConsts
    case lcs M.!? (rustifyName s) of
      Nothing -> do
        throwError $ UndefinedSymbol s
      Just n -> return (Number, owlpretty "", owlpretty n)
extractAExpr binds (AEPreimage p _ _) = do
        p' <- flattenPath p
        throwError $ PreimageInExec p'

-- The first argument (inK) is true if we are extracting the expression `k` in `let x = e in k`, false if we are extracting `e`
-- We need to track this since at the end of `k`, Rust requires us to return the itree token as well (see CRet case)

extractExpr :: Bool -> Locality -> M.Map String (RustTy, Maybe AExpr) -> CExpr -> ExtractionMonad (M.Map String (RustTy, Maybe AExpr), RustTy, OwlDoc, OwlDoc)
extractExpr inK loc binds CSkip = return (binds, Unit, owlpretty "", owlpretty "()")
extractExpr inK loc binds (CInput xsk) = do
    let ((x, ev), k) = unsafeUnbind xsk
    let rustX = rustifyName . show $ x
    let rustEv = if show ev == "_" then "_" else rustifyName . show $ ev
    (_, rt', prek, kPrettied) <- extractExpr inK loc (M.insert rustX (RcVecU8, Nothing) binds) k
    let eWrapped = owlpretty "Rc::new" <> parens (owlpretty "temp_" <> owlpretty rustX)
    typeAnnot <- do
        t <- getCurRetTy
        return $ owlpretty "::" <> angles (owlpretty t)
    let letbinding =
            owlpretty "let" <+> parens (owlpretty "temp_" <> owlpretty rustX <> comma <+> owlpretty rustEv) <+> owlpretty "=" <+> owlpretty "owl_input" <> typeAnnot <> owlpretty "(Tracked(&mut itree), &self.listener)" <> owlpretty ";" <> line <>
            owlpretty "let" <+> owlpretty rustX <+> owlpretty "=" <+> eWrapped <> owlpretty ";"
    return (binds, rt', owlpretty "", vsep [letbinding, prek, kPrettied])
extractExpr inK (Locality myLname myLidxs) binds (COutput ae lopt) = do
    (rty, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    let aePrettied' = owlpretty $ printOwlArg (rty, show aePrettied)    
    l <- case lopt of
        Nothing -> throwError OutputWithUnknownDestination
        Just (EndpointLocality (Locality lname _)) -> do
            plname <- flattenPath lname
            return $ owlpretty "&" <> owlpretty plname <> owlpretty "_addr()"
        Just (Endpoint ev) -> return $ owlpretty "&" <> (owlpretty . rustifyName . show $ ev) <> owlpretty ".as_str()"
    pmyLname <- flattenPath myLname
    typeAnnot <- do
        t <- getCurRetTy
        return $ owlpretty "::" <> angles (owlpretty t)
    let callOutput = owlpretty "owl_output" <> typeAnnot <> (parens . hsep. punctuate comma $ [owlpretty "Tracked(&mut itree)", aePrettied', l, owlpretty "&" <> owlpretty pmyLname <> owlpretty "_addr()"])
    -- The "end" of the let-binding can be an `output` call as well as a `CRet`, so we need to return the `itree` here too
    let callOutput' = if inK then tupled [callOutput, owlpretty "Tracked(itree)"] else callOutput
    return $ (binds, Unit, preAe, callOutput')
extractExpr inK loc binds (CLet e oanf xk) = do
    let (x, k) = unsafeUnbind xk
    let rustX = rustifyName . show $ x
    tempBindingLHS <- case e of 
            CCall {} -> do 
                t <- getCurRetTy
                return $ tupled [owlpretty "temp_" <> owlpretty rustX, owlpretty "Tracked(itree)"] <> 
                         owlpretty ":" <+>
                         tupled [owlpretty "_", owlpretty "Tracked<ITreeToken<" <> owlpretty t <> owlpretty ", Endpoint>>"]
            _ -> return $ owlpretty "temp_" <> owlpretty rustX 
    (_, rt, preE, ePrettied) <- extractExpr False loc binds e
    (_, rt', preK, kPrettied) <- extractExpr inK loc (M.insert rustX ((if rt == VecU8 then RcVecU8 else rt), oanf) binds) k
    let eWrapped = case rt of
            VecU8 -> owlpretty "rc_new" <> parens (owlpretty "temp_" <> owlpretty rustX)
            RcVecU8 -> rcClone <> parens (owlpretty "&temp_" <> owlpretty rustX)
            _ -> owlpretty "temp_" <> owlpretty rustX
    let letbinding = case e of
            CSkip -> owlpretty ""
            _ -> owlpretty "let" <+> tempBindingLHS <+> owlpretty "=" <+> lbrace <+> ePrettied <+> rbrace <> owlpretty ";" <> line <>
                 owlpretty "let" <+> owlpretty rustX <+> owlpretty "=" <+> eWrapped <> owlpretty ";"
    return (binds, rt', owlpretty "", vsep [preE, letbinding, preK, kPrettied])
extractExpr inK loc binds (CIf ae eT eF) = do
    (_, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    (_, rt, preeT, eTPrettied) <- extractExpr inK loc binds eT
    (_, rt', preeF, eFPrettied) <- extractExpr inK loc binds eF
    return (binds, rt, owlpretty "", preAe <> line <> owlpretty "if" <+> aePrettied <+> braces (vsep [preeT, eTPrettied]) <+> owlpretty "else" <+> braces (vsep [preeF, eFPrettied]))
extractExpr inK loc binds (CRet ae) = do
    (rt, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    let aePrettied' = if inK then tupled [aePrettied, owlpretty "Tracked(itree)"] else aePrettied
    return (binds, rt, preAe, aePrettied')
extractExpr inK loc binds (CCall owlFn (sids, pids) owlArgs) = do
    fs <- use funcs
    argsPretties <- mapM (extractAExpr binds . view val) owlArgs
    let preArgs = foldl (\p (_,s,_) -> p <> s) (owlpretty "") argsPretties
    let args = map (\sid -> (Number, sidName . show . owlpretty $ sid)) sids ++ map (\(r, _, p) -> (r, show p)) argsPretties
    powlFn <- flattenPath owlFn
    case fs M.!? powlFn of
      Nothing -> do
        throwError $ UndefinedSymbol powlFn
      Just (rt, f) -> do
        str <- f args
        return (binds, rt, preArgs, owlpretty str)
extractExpr inK loc binds (CCase ae cases) = do
   (rt, preAe, aePrettied) <- extractAExpr binds $ ae^.val
   case rt of
     Option rt' -> do
       casesPrettiedRts <- forM cases $ \(c, o) ->
               case o of
                   Left e -> do
                       (_, rt'', preE, ePrettied) <- extractExpr inK loc binds e
                       return (rt'', owlpretty c <+> owlpretty "=>" <+> braces (vsep [preE, ePrettied]))
                   Right xk -> do
                       let (x, k) = unsafeUnbind xk
                       let rustX = rustifyName . show $ x
                       (_, rt'', preK, kPrettied) <- extractExpr inK loc (M.insert rustX ((if rt' == VecU8 then RcVecU8 else rt'), Nothing) binds) k
                       let eWrapped = case rt' of
                               VecU8 -> owlpretty "rc_new" <> parens (owlpretty "temp_" <> owlpretty rustX)
                               RcVecU8 -> rcClone <> parens (owlpretty "&temp_" <> owlpretty rustX)
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
         Just s -> do return s -- debugPrint $ owlpretty "enum casing on" <+> owlpretty s; return s
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
                       (_, rt'', preE, ePrettied) <- extractExpr inK loc binds e
                       return (rt'', owlpretty b <+> owlpretty "=>" <+> braces (vsep [preE, ePrettied]))
                   Right xk -> do
                       b <- tagByteOf c
                       let (x, k) = unsafeUnbind xk
                       let rustX = rustifyName . show $ x
                       (_, rt'', preK, kPrettied) <- extractExpr inK loc (M.insert rustX (RcVecU8, Nothing) binds) k
                       let eWrapped = owlpretty "rc_new(caser_tmp.data[1..].to_vec())"
                       return (rt'', owlpretty b <+> owlpretty "=>"
                                   <+> braces (owlpretty "let" <+> owlpretty rustX <+> owlpretty "=" <+> eWrapped <> owlpretty ";" <> line <> preK <> line <> kPrettied))
       branchRt <- case casesPrettiedRts of
         [] -> throwError $ TypeError "case on enum with no cases"
         (b, _) : _ -> return b
       let defaultCase' = case branchRt of
             VecU8 -> owlpretty "vec_u8_from_elem(0,1)"
             RcVecU8 -> owlpretty "rc_new(vec_u8_from_elem(0,1))"
             Bool -> owlpretty "/* arbitrarily autogenerated */ false"
             Number -> owlpretty "/* arbitrarily autogenerated */ 0"
             String -> owlpretty "/* arbitrarily autogenerated */ \"\""
             Unit -> owlpretty "()"
             ADT s -> owlpretty "{ let mut tmp =" <+> owlpretty s <+> owlpretty "{data: rc_new(vec_u8_from_elem(0,0)), parsing_outcome:" <+> owlpretty s <> owlpretty "_ParsingOutcome::Failure}; parse_into_" <> owlpretty s <> owlpretty "(&mut tmp); tmp }"
             Option _ -> owlpretty "/* arbitrarily autogenerated */ None"
       let defaultCase = if inK then parens (defaultCase' <> owlpretty ", Tracked(itree)") else defaultCase'
       let casesPrettied = map snd casesPrettiedRts
       return (binds, branchRt, owlpretty "", preAe <> braces (
               owlpretty "let mut caser_tmp" <+> owlpretty "=" <+> 
               owlpretty (rustifyName enumOwlName) <+> lbrace <+> owlpretty "data:" <+> aePrettied <> comma <+> owlpretty "parsing_outcome:" <+> owlpretty (rustifyName enumOwlName) <> owlpretty "_ParsingOutcome::Failure" <+> rbrace <> owlpretty ";" <> line <>
               owlpretty "parse_into_" <> owlpretty (rustifyName enumOwlName)  <> parens (owlpretty "&mut caser_tmp") <> owlpretty ";" <> line <>
               owlpretty "match caser_tmp.data[0]" <+> braces (
                   vsep casesPrettied <> line <>
                   owlpretty "_ =>" <+> defaultCase <> comma
               ))
           )
extractExpr inK loc binds (CTLookup tbl ae) = do
    (rt, preAe, aePrettied) <- extractAExpr binds $ ae^.val
    aeWrapped <- case rt of
            RcVecU8 -> return $ owlpretty "&" <> aePrettied <> owlpretty ".as_slice()"
            VecU8 -> return $ owlpretty "&" <> aePrettied
            _ -> throwError $ ErrSomethingFailed "got wrong arg type for lookup"
    ptbl <- flattenPath tbl
    let tblName = rustifyName ptbl
    return (binds, Option VecU8, preAe, owlpretty "self." <> owlpretty tblName <> owlpretty ".get" <> parens aeWrapped <> owlpretty ".cloned()")
extractExpr inK loc binds (CCrypt cryptOp args) = do
    (rt, pre, opPrettied) <- extractCryptOp binds cryptOp args
    let opPrettied' = if inK then tupled [opPrettied, owlpretty "Tracked(itree)"] else opPrettied
    return (binds, rt, pre, opPrettied')
extractExpr inK loc binds (CIncCtr ctr idxs) = do
    pctr <- flattenPath ctr
    let ctrName = owlpretty "mut_state." <> owlpretty (rustifyName pctr)
    let incr = 
            owlpretty "if" <+> ctrName <+> owlpretty "> usize::MAX - 1 { return Err(OwlError::IntegerOverflow); }" <> owlpretty ";" <> line <> 
            ctrName <+> owlpretty "=" <+> ctrName <+> owlpretty "+ 1;"
    return (binds, Unit, owlpretty "", line <> incr)
extractExpr inK loc binds (CGetCtr ctr idxs) = do
    pctr <- flattenPath ctr
    let ctrName = owlpretty "mut_state." <> owlpretty (rustifyName pctr)
    return (binds, Number, owlpretty "", ctrName)
extractExpr inK loc binds c = throwError $ ErrSomethingFailed $ "unimplemented case for extractExpr: " ++ (show . owlpretty $ c)

funcCallPrinter :: String -> [(String, RustTy)] -> RustTy -> [(RustTy, String)] -> ExtractionMonad String
funcCallPrinter owlName rustArgs retTy callArgs = do
    let callMacro = case retTy of
            Option _ -> "owl_call_ret_option!"
            _ -> "owl_call!"
    if length rustArgs == length callArgs then
        return $ show $ owlpretty callMacro <> tupled [
              owlpretty "itree"
            , owlpretty "*mut_state"
            , owlpretty owlName <> owlpretty "_spec" <>
                tupled (owlpretty "*self" : owlpretty "*mut_state" : (map (\(rty, arg) -> owlpretty (viewVar rty (unclone arg))) $ callArgs))
            , owlpretty "self." <> owlpretty (rustifyName owlName) <>
                tupled (owlpretty "mut_state" : (map (\(rty, arg) -> owlpretty arg) $ callArgs))
        ]
    else throwError $ TypeError $ "got wrong args for call to " ++ owlName
    where
        unclone str = fromMaybe str (stripPrefix "rc_clone" str)

extractArg :: (String, RustTy) -> OwlDoc
extractArg (s, rt) =
    owlpretty s <> owlpretty ":" <+> owlpretty rt

rustifyArg :: (DataVar, Embed Ty) -> ExtractionMonad (String, RustTy)
rustifyArg (v, t) = do
    rt <- rustifyArgTy . doConcretifyTy . unembed $ t
    return (rustifyName $ show v, rt)

-- rustifySidArg :: IdxVar -> (String, RustTy)
-- rustifySidArg v =
--     (sidName . show $ v, Number)

makeFunc :: String -> Locality -> [(DataVar, Embed Ty)] -> Ty  -> ExtractionMonad ()
makeFunc owlName _ owlArgs owlRetTy = do
    let name = rustifyName owlName
    rustArgs <- mapM rustifyArg owlArgs
    rtb <- rustifyRetTy $ doConcretifyTy owlRetTy
    funcs %= M.insert owlName (rtb, funcCallPrinter owlName rustArgs rtb)
    return ()


-- The `owlBody` is expected to *not* be in ANF yet (for extraction purposes)
-- the last `bool` argument is if this is the main function for this locality, in which case we additionally return a wrapper for the entry point
extractDef :: String -> Locality -> [(DataVar, Embed Ty)] -> Ty -> Expr -> Bool -> ExtractionMonad (OwlDoc, OwlDoc)
extractDef owlName loc owlArgs owlRetTy owlBody isMain = do
    debugPrint $ "Extracting def " ++ owlName 
    let name = rustifyName owlName
    let (Locality lpath _) = loc
    lname <- flattenPath lpath
    concreteBody <- concretify owlBody
    -- debugPrint $ owlpretty concreteBody
    anfBody <- concretify =<< ANF.anf owlBody
    -- debugPrint $ owlpretty anfBody
    rustArgs <- mapM rustifyArg owlArgs
    -- let rustSidArgs = map rustifySidArg sidArgs
    rtb <- rustifyArgTy $ doConcretifyTy owlRetTy
    curRetTy .= (Just . show $ parens (owlpretty (specTyOf rtb) <> comma <+> owlpretty (stateName lname)))
    (_, rtb, preBody, body) <- extractExpr True loc (M.fromList . map (\(s,r) -> (s, (r, Nothing))) $ rustArgs) anfBody
    curRetTy .= Nothing
    decl <- genFuncDecl name lname rustArgs rtb
    defSpec <- Spec.extractDef owlName loc concreteBody owlArgs (specTyOf rtb)
    let mainWrapper = if isMain then genMainWrapper owlName lname rtb (specTyOf rtb) else owlpretty ""
    return $ (
        decl <+> lbrace <> line <> 
            unwrapItreeArg <> intoOk (preBody <> line <> body <> line) <>
        rbrace <> line <> line <> 
        mainWrapper
        , defSpec)
    where
        specRtPrettied specRt lname = owlpretty "<(" <> owlpretty specRt <> comma <+> owlpretty (stateName lname) <> owlpretty "), Endpoint>"
        genFuncDecl name lname owlArgs rt = do
            let itree = owlpretty "Tracked<ITreeToken" <> specRtPrettied (specTyOf rt) lname <> owlpretty ">"
            let argsPrettied = hsep . punctuate comma $ 
                    owlpretty "&self"
                    : owlpretty "Tracked(itree):" <+> itree
                    : owlpretty "mut_state: &mut" <+> owlpretty (stateName lname)
                    -- : map (\(a,_) -> owlpretty a <+> owlpretty ": usize") sidArgs
                    : map extractArg owlArgs
            let rtPrettied = owlpretty "->" <+> parens (owlpretty "res: Result<" <> tupled [owlpretty rt, itree] <> owlpretty ", OwlError>")
            let viewRes = parens $ 
                    (case rt of
                        Unit -> owlpretty "()"
                        ADT _ -> owlpretty "res.get_Ok_0().0.data.view()"
                        Option (ADT _) -> owlpretty "view_option(res.get_Ok_0().0).data"
                        Option _ -> owlpretty "view_option(res.get_Ok_0().0)"
                        _ -> owlpretty "res.get_Ok_0().0.view()")
                    <> owlpretty ", *mut_state"
            let defReqEns =
                    owlpretty "requires itree@ ==" <+> owlpretty owlName <> owlpretty "_spec" <> tupled (owlpretty "*self" : owlpretty "*old(mut_state)" : map (\(s,t) -> owlpretty $ viewVar t s) owlArgs) <> line <>
                    owlpretty "ensures  res.is_Ok() ==> (res.get_Ok_0().1)@@.results_in" <> parens viewRes <> line 
            return $ owlpretty "pub fn" <+> owlpretty name <> parens argsPrettied <+> rtPrettied <> line <> defReqEns
        unwrapItreeArg = owlpretty "let tracked mut itree = itree;"
        intoOk rustExpr = owlpretty "let res_inner = {" <> line <> line <> rustExpr <> line <> line <> owlpretty "};" <> line <> owlpretty "Ok(res_inner)"
        genMainWrapper owlName lname execRetTy specRetTy = 
            owlpretty "#[verifier(external_body)] pub exec fn" <+> owlpretty (rustifyName owlName) <> owlpretty "_wrapper" <> 
            parens (owlpretty "&self, s: &mut" <+> owlpretty (stateName lname)) <> owlpretty "->" <> parens (owlpretty "_:" <+> owlpretty execRetTy) <> braces (line <>
                owlpretty "let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<(), Endpoint>::dummy_itree_token();" <> line <>
                owlpretty "let tracked (Tracked(call_token), _) = split_bind(dummy_tok," <+>  owlpretty owlName <> owlpretty "_spec(*self, *s)" <> owlpretty ");" <> line <>

                owlpretty "let (res,_):" <+> tupled [owlpretty execRetTy, owlpretty "Tracked<ITreeToken" <> specRtPrettied specRetTy lname <> owlpretty ">"] <+> owlpretty "=" <+>
                    owlpretty "self." <> owlpretty (rustifyName owlName) <> parens (owlpretty "Tracked(call_token), s, /* todo args? */") <> owlpretty ".unwrap();" <> line <>
                owlpretty "res" <>
            line)

nameInit :: String -> NameType -> ExtractionMonad (OwlDoc)
nameInit s nt = case nt^.val of
    NT_Nonce -> return $ owlpretty "let" <+> owlpretty (rustifyName s) <+> owlpretty "=" <+> owlpretty "owl_aead::gen_rand_nonce(cipher());"
    NT_Enc _ -> return $ owlpretty "let" <+> owlpretty (rustifyName s) <+> owlpretty "=" <+> owlpretty "owl_aead::gen_rand_key(cipher());"
    NT_StAEAD {} -> 
                return $ owlpretty "let" <+> owlpretty (rustifyName s) <+> owlpretty "=" <+> owlpretty "owl_aead::gen_rand_key(cipher());"
    NT_MAC _ -> return $ owlpretty "let" <+> owlpretty (rustifyName s) <+> owlpretty "=" <+> owlpretty "owl_hmac::gen_rand_key(&hmac_mode());"
    NT_PKE _ -> return $ owlpretty "let" <+> (parens . hsep . punctuate comma . map owlpretty $ [rustifyName s, "pk_" ++ rustifyName s]) <+> owlpretty "=" <+> owlpretty "owl_pke::gen_rand_keys();"
    NT_Sig _ -> return $ owlpretty "let" <+> (parens . hsep . punctuate comma . map owlpretty $ [rustifyName s, "pk_" ++ rustifyName s]) <+> owlpretty "=" <+> owlpretty "owl_pke::gen_rand_keys();"
    NT_DH ->    return $ owlpretty "let" <+> (parens . hsep . punctuate comma . map owlpretty $ [rustifyName s, "pk_" ++ rustifyName s]) <+> owlpretty "=" <+> owlpretty "owl_dhke::gen_ecdh_key_pair();"
    _ -> throwError $ ErrSomethingFailed "unimplemented name initializer"


-------------------------------------------------------------------------------------------
-- Handling localities

type LocalityName = String
type NameData = (String, NameType, Int) -- name, type, number of processID indices
type DefData = (String, Locality, [(DataVar, Embed Ty)], Ty, Expr) -- func name, locality, arguments, return type, body
type LocalityData = (Int, [NameData], [NameData], [DefData], [(String, Ty)], [String]) -- number of locality indices, local state, shared state, defs, table names and codomains, names of counters


-- returns (locality stuff, shared names, public keys)
preprocessModBody :: TB.ModBody -> ExtractionMonad (M.Map LocalityName LocalityData, [(NameData, [(LocalityName, Int)])], [NameData])
preprocessModBody mb = do
    let (locs, locAliases) = sortLocs $ mb ^. TB.localities
    let lookupLoc = lookupLoc' locs locAliases
    let locMap = M.map (\npids -> (npids, [],[],[],[], [])) locs
    locMap <- foldM (sortDef lookupLoc) locMap (mb ^. TB.defs)
    locMap <- foldM (sortTable lookupLoc) locMap (mb ^. TB.tableEnv)
    locMap <- foldM (sortCtr lookupLoc) locMap (mb ^. TB.ctrEnv)
    (locMap, shared, pubkeys) <- foldM (sortName lookupLoc) (locMap, [], []) (mb ^. TB.nameDefs)
    -- mapM_ sortOrcl $ (mb ^. TB.randomOracle)
    -- TODO counters
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
                when (length sids > 1) $ throwError $ DefWithTooManySids owlName
                let loc@(Locality locP _) = defspec ^. TB.defLocality
                locName <- lookupLoc =<< flattenPath locP
                let (args, (_, retTy, body)) = unsafeUnbind (defspec ^. TB.preReq_retTy_body) 
                case body of
                    Nothing -> return m
                    Just e  -> do
                        let f (i, l, s, d, t, c) = (i, l, s, d ++ [(owlName, loc, args, retTy, e)], t, c)
                        makeFunc owlName loc args retTy
                        return $ M.adjust f locName m
        
        sortTable :: (LocalityName -> ExtractionMonad LocalityName) -> M.Map LocalityName LocalityData -> (String, (Ty, Locality)) -> ExtractionMonad (M.Map LocalityName LocalityData)
        sortTable lookupLoc locMap (name, (ty, Locality locP _)) = do
            locName <- lookupLoc =<< flattenPath locP
            let f (i, l, s, d, t, c) = (i, l, s, d, t ++ [(name, ty)], c)
            return $ M.adjust f locName locMap

        sortCtr :: (LocalityName -> ExtractionMonad LocalityName) -> M.Map LocalityName LocalityData -> (String, Bind ([IdxVar], [IdxVar]) Locality) -> ExtractionMonad (M.Map LocalityName LocalityData)
        sortCtr lookupLoc locMap (name, b) = do
            let ((sids, pids), Locality locP _) = unsafeUnbind b
            case (sids, pids) of
                ([], _) -> do
                    locName <- lookupLoc =<< flattenPath locP
                    let f (i, l, s, d, t, c) = (i, l, s, d, t, c ++ [name])
                    return $ M.adjust f locName locMap
                _ -> throwError $ ErrSomethingFailed "TODO indexed counters"

        sortName :: (LocalityName -> ExtractionMonad LocalityName) 
                    -> (M.Map LocalityName LocalityData, [(NameData, [(LocalityName, Int)])], [NameData]) 
                    -> (String, (Bind ([IdxVar], [IdxVar]) TB.NameDef))
                    -> ExtractionMonad (M.Map LocalityName LocalityData, [(NameData, [(LocalityName, Int)])], [NameData]) 
        sortName lookupLoc (locMap, shared, pubkeys) (name, binds) = do
            let ((sids, pids), nd) = unsafeUnbind binds
            case nd of
              TB.AbstractName -> return (locMap, shared, pubkeys) -- ignore abstract names, they should be concretized when used
              TB.RODef _ b -> do
                let (_, (arg, _, rtys)) = unsafeUnbind b
                (totLen, sliceMap) <- foldM (\(t, m) (i, rty) -> do
                        rtstr <- case rty ^. val of
                            NT_Nonce -> return "nonce"
                            NT_Enc _ -> return "enckey"
                            NT_StAEAD {} -> return "enckey"
                            _ -> throwError $ UnsupportedOracleReturnType name
                        return (t ++ [rtstr], M.insert i (t, t ++ [rtstr]) m)
                    ) (["0"], M.empty) (zip [0..] rtys)
                oracles %= M.insert name (totLen, sliceMap)
                return (locMap, shared, pubkeys) -- RO defs go in a separate data structure
              TB.BaseDef (nt, loc) -> do
                nameLen <- case nt ^. val of
                    NT_Nonce -> do useAeadNonceSize
                    NT_Enc _ -> do useAeadKeySize
                    NT_StAEAD {} -> do useAeadKeySize
                    NT_MAC _ -> do useHmacKeySize
                    NT_PKE _ -> do return pkeKeySize
                    NT_Sig _ -> do return sigKeySize
                    NT_DH -> return dhSize
                    _ -> do
                        throwError $ UnsupportedNameType nt
                let nsids = length sids
                let npids = length pids
                when (nsids > 1) $ throwError $ DefWithTooManySids name
                typeLayouts %= M.insert (rustifyName name) (LBytes nameLen)
                let gPub m lo = M.adjust (\(i,l,s,d,t,c) -> (i, l, s ++ [(name, nt, npids)], d, t, c)) lo m
                let gPriv m lo = M.adjust (\(i,l,s,d,t,c) -> (i, l ++ [(name, nt, npids)], s, d, t, c)) lo m
                locNames <- mapM (\(Locality lname _) -> flattenPath lname) loc
                locNameCounts <- mapM (\(Locality lname lidxs) -> do
                    plname <- flattenPath lname
                    return (plname, length lidxs)) loc
                case nt ^.val of
                    -- public keys must be shared, so pub/priv key pairs are generated by the initializer
                    NT_PKE _ ->
                        return (foldl gPub locMap locNames, shared ++ [((name, nt, npids), locNameCounts)], pubkeys ++ [(name, nt, npids)])
                    NT_Sig _ ->
                        return (foldl gPub locMap locNames, shared ++ [((name, nt, npids), locNameCounts)], pubkeys ++ [(name, nt, npids)])
                    NT_DH ->
                        return (foldl gPub locMap locNames, shared ++ [((name, nt, npids), locNameCounts)], pubkeys ++ [(name, nt, npids)])
                    _ -> if length loc /= 1 then
                            -- name is shared among multiple localities
                            return (foldl gPub locMap locNames, shared ++ [((name, nt, npids), locNameCounts)], pubkeys)
                        else
                            -- name is local and can be locally generated
                            return (foldl gPriv locMap locNames, shared, pubkeys)

        -- sortOrcl :: (String, (Bind [IdxVar] ([AExpr], [NameType]))) -> ExtractionMonad ()
        -- sortOrcl (n, b) = do
        --     let (_, (args, rtys)) = unsafeUnbind b
        --     rtlen <- case (map (view val) rtys) of
        --         [NT_Nonce] -> return "nonce_size()"
        --         [NT_Enc _] -> return "key_size()"
        --         _ -> throwError $ UnsupportedOracleReturnType n
        --     oracles %= M.insert n rtlen


-- return (main func name, exec code, spec code, unverified lib code)
extractLoc :: [NameData] -> (LocalityName, LocalityData) -> ExtractionMonad (String, OwlDoc, OwlDoc, OwlDoc)
extractLoc pubKeys (loc, (idxs, localNames, sharedNames, defs, tbls, ctrs)) = do
    -- check name sharing is ok
    mapM_ (\(n,_,npids) -> unless (npids == 0 || (idxs == 1 && npids == 1)) $ throwError $ UnsupportedSharedIndices n) sharedNames
    let sfs = cfgFields idxs localNames sharedNames pubKeys tbls
    let cfs = configFields idxs sharedNames pubKeys
    let mfs = mutFields ctrs
    -- indexedNameGetters <- mapM genIndexedNameGetter localNames
    -- let sharedIndexedNameGetters = map genSharedIndexedNameGetter sharedNames
    initLoc <- genInitLoc loc localNames sharedNames pubKeys tbls
    let initMutState = genInitMutState loc ctrs
    let configDef = configLibCode loc cfs
    case find (\(n,_,as,_,_) -> isSuffixOf "_main" n && null as) defs of
        Just (mainName,_,_,_,_) -> do
            (fns, fnspecs) <- unzip <$> mapM (\(n, l, as, t, e) -> extractDef n l as t e (n == mainName)) defs
            return (rustifyName mainName,
                owlpretty "pub struct" <+> owlpretty (stateName loc) <+> braces mfs <> line <>
                owlpretty "impl" <+> owlpretty (stateName loc) <+> braces (line <> initMutState) <>
                owlpretty "pub struct" <+> owlpretty (cfgName loc) <+> braces sfs <> line <>
                owlpretty "impl" <+> owlpretty (cfgName loc) <+> braces (line <> initLoc <+> vsep ({- indexedNameGetters ++ sharedIndexedNameGetters ++ -} fns)),
                vsep fnspecs,
                configDef)
        Nothing -> throwError $ LocalityWithNoMain loc
    where
        -- genIndexedNameGetter (n, nt, nsids, _) = if nsids == 0 then return $ owlpretty "" else do
        --     ni <- nameInit n nt
        --     return $
        --         owlpretty "pub fn get_" <> owlpretty (rustifyName n) <> tupled (owlpretty "&mut self" : [owlpretty "sid" <> owlpretty n <> owlpretty ": usize" | n <- [0..(nsids-1)]]) <+> owlpretty "-> Rc<Vec<u8>>" <> lbrace <> line <>
        --             owlpretty "match self." <> owlpretty (rustifyName n) <> owlpretty ".get" <> parens (tupled ([owlpretty "&sid" <> owlpretty n | n <- [0..(nsids-1)]])) <> lbrace <> line <>
        --                 owlpretty "Some(v) =>" <+> rcClone <> owlpretty "(v)," <> line <>
        --                 owlpretty "None =>" <+> lbrace <> line <>
        --                     ni <> line <>
        --                     owlpretty "let v = rc_new" <> parens (owlpretty (rustifyName n)) <> owlpretty ";" <> line <>
        --                     owlpretty "self." <> owlpretty (rustifyName n) <> owlpretty ".insert" <> parens (tupled ([owlpretty "sid" <> owlpretty n | n <- [0..(nsids-1)]]) <> comma <+> rcClone <> owlpretty "(&v)") <> owlpretty ";" <> line <>
        --                     rcClone <> owlpretty "(&v)" <> line <>
        --                 rbrace <>
        --             rbrace <>
        --         rbrace
        -- genSharedIndexedNameGetter (n, _, nsids, _) = if nsids == 0 then owlpretty "" else
        --     owlpretty "pub fn get_" <> owlpretty (rustifyName n) <> tupled (owlpretty "&self" : [owlpretty "sid" <> owlpretty n <> owlpretty ": usize" | n <- [0..(nsids-1)]]) <+> owlpretty "-> Rc<Vec<u8>>" <> lbrace <> line <>
        --         rcClone <> parens (owlpretty "&self." <> owlpretty (rustifyName n)) <>
        --     rbrace

        configLibCode loc cfs =
            owlpretty "#[derive(Serialize, Deserialize)]" <> line <> owlpretty "pub struct" <+> owlpretty (cfgName loc) <> owlpretty "_config" <+> braces cfs <> line <>
            serdeWrappers loc

        serdeWrappers loc =
            let l = owlpretty (cfgName loc) in
            owlpretty "pub fn serialize_" <> l <> owlpretty "_config(l: &" <> l <> owlpretty "_config) -> String" <> braces (line <>
                owlpretty "serde_json::to_string(&l).expect(\"Can't serialize "<> l <> owlpretty "_config\")" <> line
            ) <> line <> 
            owlpretty "pub fn deserialize_" <> l <> owlpretty "_config<'a>(s: &'a str) -> " <> l <> owlpretty "_config" <> braces (line <>
                owlpretty "serde_json::from_str(s).expect(\"Can't deserialize "<> l <> owlpretty "_config\")" <> line
            )

        configFields idxs sharedNames pubKeys =
            vsep . punctuate comma $
                map (\(s,_,npids) -> owlpretty "pub" <+> owlpretty (rustifyName s) <> owlpretty ": Vec<u8>") sharedNames ++
                map (\(s,_,_) -> owlpretty "pub" <+>  owlpretty "pk_" <> owlpretty (rustifyName s) <> owlpretty ": Vec<u8>") pubKeys ++
                [owlpretty "pub" <+> owlpretty "salt" <> owlpretty ": Vec<u8>"]
        cfgFields idxs localNames sharedNames pubKeys tbls =
            vsep . punctuate comma $
                owlpretty "pub listener: TcpListener" :
                map (\(s,_,npids) -> owlpretty "pub" <+> owlpretty (rustifyName s) <> owlpretty ": Rc<Vec<u8>>") localNames ++
                map (\(s,_,npids) -> owlpretty "pub" <+> owlpretty (rustifyName s) <> (if npids == 0 || (idxs == 1 && npids == 1) then owlpretty ": Rc<Vec<u8>>" else owlpretty ": Rc<HashMap<usize, Vec<u8>>>")) sharedNames ++
                map (\(s,_,_) -> owlpretty "pub" <+> owlpretty "pk_" <> owlpretty (rustifyName s) <> owlpretty ": Rc<Vec<u8>>") pubKeys ++
                -- Tables are always treated as local:
                map (\(n,t) -> owlpretty "pub" <+> owlpretty (rustifyName n) <> owlpretty ": HashMap<Vec<u8>, Vec<u8>>") tbls ++
                [owlpretty "pub" <+> owlpretty "salt" <> owlpretty ": Rc<Vec<u8>>"]
        mutFields ctrs = 
            vsep . punctuate comma $ 
                map (\n -> owlpretty "pub" <+> owlpretty (rustifyName n) <> owlpretty ": usize") ctrs
        genInitLoc loc localNames sharedNames pubKeys tbls = do
            localInits <- mapM (\(s,n,_) -> nameInit s n) localNames 
            return $ owlpretty "#[verifier(external_body)] pub fn init_" <> owlpretty (cfgName loc) <+> parens (owlpretty "config_path : &StrSlice") <+> owlpretty "-> Self" <+> lbrace <> line <>
                owlpretty "let listener = TcpListener::bind" <> parens (owlpretty loc <> owlpretty "_addr().into_rust_str()") <> owlpretty ".unwrap();" <> line <>
                vsep localInits <> line <>
                owlpretty "let config_str = fs::read_to_string(config_path.into_rust_str()).expect(\"Config file not found\");" <> line <>
                owlpretty "let config =" <+> owlpretty "deserialize_" <> owlpretty (cfgName loc) <> owlpretty "_config(&config_str);" <> line <>
                owlpretty "return" <+> owlpretty (cfgName loc) <+>
                    braces (hsep . punctuate comma $
                        owlpretty "listener"  :
                        map (\(s,_,_) ->
                                (owlpretty . rustifyName $ s) <+> owlpretty ":" <+> owlpretty "rc_new" <> parens (owlpretty . rustifyName $ s)
                            ) localNames ++
                        map (\(s,_,_) -> owlpretty (rustifyName s) <+> owlpretty ":" <+> owlpretty "rc_new" <> parens (owlpretty "config." <> owlpretty (rustifyName s))) sharedNames ++
                        map (\(s,_,_) -> owlpretty "pk_" <> owlpretty (rustifyName s) <+> owlpretty ":" <+> owlpretty "rc_new" <> parens (owlpretty "config." <> owlpretty "pk_" <> owlpretty (rustifyName s))) pubKeys ++
                        map (\(n,_) -> owlpretty (rustifyName n) <+> owlpretty ":" <+> owlpretty "HashMap::new()") tbls ++
                        [owlpretty "salt : rc_new(config.salt)"]
                    ) <>
                rbrace
        genInitMutState loc ctrs = 
            let ctrInits = map (\n -> owlpretty (rustifyName n) <+> owlpretty ": 0,") ctrs in
            owlpretty "#[verifier(external_body)] pub fn init_" <> owlpretty (stateName loc) <+> parens (owlpretty "") <+> owlpretty "-> Self" <+> lbrace <> line <> 
                owlpretty (stateName loc) <+> braces (vsep ctrInits)
            <> rbrace


-- returns (index map, executable code, spec code, unverified lib code)
extractLocs :: [NameData] ->  M.Map LocalityName LocalityData -> ExtractionMonad (M.Map LocalityName String, OwlDoc, OwlDoc, OwlDoc)
extractLocs pubkeys locMap = do
    let addrs = mkAddrs 0 $ M.keys locMap
    (sidArgMap, ps, spec_ps, ls) <- foldM (go pubkeys) (M.empty, [], [], []) $ M.assocs locMap
    let specEndpoint = Spec.mkSpecEndpoint $ M.keys locMap
    return (sidArgMap, 
            addrs <> line <> vsep ps, 
            specEndpoint <> line <> Spec.endpointOfAddr <> line <> line <> (vsep . punctuate line $ spec_ps),
            vsep . punctuate line $ ls)
    where
        go pubKeys (m, ps, ss, ls) (lname, ldata) = do
            (mainName, p, s, l) <- extractLoc pubKeys (lname, ldata)
            return (M.insert lname mainName m, ps ++ [p], ss ++ [s], ls ++ [l])
        mkAddrs :: Int -> [LocalityName] -> OwlDoc
        mkAddrs n [] = owlpretty ""
        mkAddrs n (l:locs) =
            owlpretty "#[verifier(external_body)] pub const fn" <+> owlpretty l <> owlpretty "_addr() -> (a:StrSlice<'static>)" <> line <>
                owlpretty "ensures endpoint_of_addr(a.view()) ==" <+> owlpretty "Endpoint::Loc_" <> owlpretty l <> line <> 
            braces (line <> owlpretty "new_strlit" <> parens (dquotes (owlpretty "127.0.0.1:" <> owlpretty (9001 + n))) <> line) <> line <>
            mkAddrs (n+1) locs

entryPoint :: M.Map LocalityName LocalityData -> [(NameData, [(LocalityName, Int)])] -> [NameData] -> M.Map LocalityName String -> ExtractionMonad (OwlDoc)
entryPoint locMap sharedNames pubKeys mainNames = do
    let allLocs = M.keys locMap
    sharedNameInits <- mapM genSharedNameInit sharedNames
    let salt = genSalt
    let writeConfigs = map (writeConfig (map (\(p,_,_) -> p) pubKeys)) $ M.assocs locMap
    -- let idxLocCounts = map genIdxLocCount $ M.assocs locMap
    let config = owlpretty "if" <+> (hsep . punctuate (owlpretty " && ") . map owlpretty $ ["args.len() >= 3", "args[1] == \"config\""]) <>
            (braces . vsep $ [{- vsep idxLocCounts, -} vsep sharedNameInits, salt, vsep writeConfigs]) <> owlpretty "else"
    allLocsMainNames <- mapM (\l -> do
                                    let nSidArgs = mainNames M.!? l
                                    case nSidArgs of
                                        Just m -> return (l, m)
                                        Nothing -> throwError $ ErrSomethingFailed $ "couldn't look up main function name for " ++ l ++ ", bug in extraction"
                            ) allLocs
    let runLocs = map genRunLoc allLocsMainNames
    return $ owlpretty "#[verifier(external_body)] #[allow(unreachable_code)] #[allow(unused_variables)]" <> line <> owlpretty "fn entrypoint()" <+> lbrace <> line <>
        owlpretty "let args: std::vec::Vec<std::string::String> = env::args().collect();" <> line <>
        vsep runLocs <> line <>
        config <>
        braces (owlpretty "println!(\"Incorrect usage\");") <> line <>
        rbrace <> line <> line 
    where
        -- genIdxLocCount (lname, (npids,_,_,_,_,_)) =
        --     if npids == 0 then owlpretty "" else
        --         owlpretty "let n_" <> owlpretty (locName lname) <+> owlpretty "= get_num_from_cmdline" <> (parens . dquotes $ owlpretty lname) <> owlpretty ";"

        genSharedNameInit ((name, nt, _), locs) = do
            let rName = rustifyName name
            let nTotalPids = sum . map snd $ locs
            if nTotalPids == 0 || nTotalPids == 1 then
                nameInit name nt
            -- else if nTotalPids == 1 then do
            --     idxLocName <- case find (\(_,n) -> n == 1) locs of
            --                     Just (l,_) -> return l
            --                     Nothing -> throwError $ ErrSomethingFailed "should be unreachable"
            --     ni <- nameInit "tmp" nt
            --     return $ owlpretty "let mut" <+> owlpretty (rustifyName name) <+> owlpretty "= HashMap::new();" <> line <>
            --         owlpretty "for i in 0..n_" <> owlpretty (locName idxLocName) <> braces (ni <+> owlpretty (rustifyName name) <> owlpretty ".insert(i, owl_tmp);")
            else throwError $ UnsupportedSharedIndices "can't have a name shared by multiple PID-parameterized localities"

        genSalt = owlpretty "let" <+> owlpretty "salt" <+> owlpretty "=" <+> owlpretty "owl_util::gen_rand_bytes(64);" -- use 64 byte salt

        writeConfig pubKeys (loc, (npids, _, ss, _, _, _)) =
            let configInits = hsep . punctuate comma $
                    (map (\(n,_,_) -> owlpretty (rustifyName n) <+> owlpretty ":" <+> owlpretty (rustifyName n) <> (if npids == 0 then owlpretty "" else owlpretty ".get(&i).unwrap()") <> owlpretty ".clone()") ss ++
                     map (\n -> owlpretty "pk_" <> owlpretty (rustifyName n) <+> owlpretty ":" <+> owlpretty "pk_" <> owlpretty (rustifyName n) <> owlpretty ".clone()") pubKeys ++
                     [owlpretty "salt" <+> owlpretty ":" <+> owlpretty "salt" <> owlpretty ".clone()"]) in
            -- (if npids == 0 then owlpretty "" else owlpretty "for i in 0..n_" <> owlpretty (locName loc) <+> lbrace) <>
            owlpretty "let" <+> owlpretty (cfgName loc) <> owlpretty "_config:" <+> owlpretty (cfgName loc) <> owlpretty "_config" <+> owlpretty "=" <+> owlpretty (cfgName loc) <> owlpretty "_config" <+> braces configInits <> owlpretty ";" <> line <>
            owlpretty "let" <+> owlpretty (cfgName loc) <> owlpretty "_config_serialized" <+> owlpretty "=" <+>
                    owlpretty "serialize_" <> owlpretty (cfgName loc) <> owlpretty "_config" <> parens (owlpretty "&" <> owlpretty (cfgName loc) <> owlpretty "_config") <> owlpretty ";" <> line <>
            owlpretty "let mut" <+> owlpretty (cfgName loc) <> owlpretty "_f" <+> owlpretty "=" <+>
                owlpretty "fs::File::create(format!(\"{}/{}" {- <> (if npids == 0 then owlpretty "" else owlpretty "_{}") -} <> owlpretty ".owl_config\", &args[2]," <+> 
                    dquotes (owlpretty (cfgName loc)) {- <> (if npids == 0 then owlpretty "" else owlpretty ",i") -} <> owlpretty ")).expect(\"Can't create config file\");" <> line <>
            owlpretty (cfgName loc) <> owlpretty "_f" <> owlpretty ".write_all" <> parens (owlpretty (cfgName loc) <> owlpretty "_config_serialized.as_bytes()")
                                <> owlpretty ".expect(\"Can't write config file\");"
            -- (if npids == 0 then owlpretty "" else rbrace)

        genRunLoc (loc, mainName) =
            let body = genRunLocBody loc mainName in
            -- owlpretty "if" <+> (hsep . punctuate (owlpretty " && ") . map owlpretty $ 
            --         ["args.len() >= 4", "args.index(1).as_str().into_rust_str() == \"run\"", "args.index(2).as_str().into_rust_str() == \"" ++ loc ++ "\""]) <>                
            owlpretty "if" <+> (hsep . punctuate (owlpretty " && ") . map owlpretty $ ["args.len() >= 4", "args[1] == \"run\"", "args[2] == \"" ++ loc ++ "\""]) <>
                braces body <> owlpretty "else"
        genRunLocBody loc mainName =
            owlpretty "let loc =" <+> owlpretty (cfgName loc) <> owlpretty "::init_" <> owlpretty (cfgName loc) <>
                -- parens (owlpretty "&args.index(3)") <> owlpretty ";" <> line <>
                parens (owlpretty "&String::from_rust_string(args[3].clone()).as_str()") <> owlpretty ";" <> line <>
            owlpretty "let mut mut_state =" <+> owlpretty (stateName loc) <> owlpretty "::init_" <> owlpretty (stateName loc) <> owlpretty "();" <> line <>
            owlpretty "println!(\"Waiting for 5 seconds to let other parties start...\");" <> line <>
            owlpretty "thread::sleep(Duration::new(5, 0));" <> line <>
            owlpretty "println!(\"Running" <+> owlpretty mainName <+> owlpretty "...\");" <> line <>
            owlpretty "let now = Instant::now();" <> line <>
            owlpretty "let res = loc." <> owlpretty mainName <> owlpretty "_wrapper" <> tupled ([owlpretty "&mut mut_state"] {- : [owlpretty i | i <- [1..nSidArgs]] -}) <> owlpretty ";" <> line <>
            owlpretty "let elapsed = now.elapsed();" <> line <>
            owlpretty "println!" <> parens (dquotes (owlpretty loc <+> owlpretty "returned ") <> owlpretty "/*" <> owlpretty "," <+> owlpretty "res" <> owlpretty "*/") <> owlpretty ";" <> line <>
            owlpretty "println!" <> parens (dquotes (owlpretty "Elapsed: {:?}") <> owlpretty "," <+> owlpretty "elapsed") <> owlpretty ";"


-------------------------------------------------------------------------------------------
--- Entry point of extraction


extractTyDefs :: [(TyVar, TB.TyDef)] -> ExtractionMonad (OwlDoc, OwlDoc)
extractTyDefs [] = return $ (owlpretty "", owlpretty "")
extractTyDefs ((tv, td):ds) = do
    (dExtracted, sExtracted) <- extractTyDef tv td
    (dsExtracted, ssExtracted) <- extractTyDefs ds
    return $ (dExtracted <> line <> line <> dsExtracted, sExtracted <> line <> line <> ssExtracted)
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
            return $ (owlpretty "", owlpretty "")
        extractTyDef name TB.TyAbstract = do
            typeLayouts %= M.insert (rustifyName name) (LBytes 0) -- Replaced later when instantiated
            return $ (owlpretty "", owlpretty "")

owlprettyFile :: String -> ExtractionMonad (OwlDoc)        
owlprettyFile fn = do
    s <- liftIO $ readFile fn
    return $ owlpretty s

extractModBody :: TB.ModBody -> ExtractionMonad (OwlDoc, OwlDoc) 
extractModBody mb = do
    (locMap, sharedNames, pubKeys) <- preprocessModBody mb
    -- We get the list of tyDefs in reverse order of declaration, so reverse again
    (tyDefsExtracted, specTyDefsExtracted) <- extractTyDefs $ reverse (mb ^. TB.tyDefs)
    (mainNames, locsExtracted, locSpecsExtracted, libCode) <- extractLocs pubKeys locMap
    p <- owlprettyFile "extraction/preamble.rs"
    lp <- owlprettyFile "extraction/lib_preamble.rs"
    ep <- entryPoint locMap sharedNames pubKeys mainNames
    return (
        p                       <> line <> line <> line <> line <> 
        owlpretty "verus! {"       <> line <> line <> 
        owlpretty "// ------------------------------------" <> line <>
        owlpretty "// ---------- SPECIFICATIONS ----------" <> line <>
        owlpretty "// ------------------------------------" <> line <> line <>
        specTyDefsExtracted     <> line <> line <>
        locSpecsExtracted       <> line <> line <> line <> line <>
        owlpretty "// ------------------------------------" <> line <>
        owlpretty "// ---------- IMPLEMENTATIONS ---------" <> line <>
        owlpretty "// ------------------------------------" <> line <> line <>
        tyDefsExtracted         <> line <> line <>
        locsExtracted           <> line <> line <>
        owlpretty "// ------------------------------------" <> line <>
        owlpretty "// ------------ ENTRY POINT -----------" <> line <>
        owlpretty "// ------------------------------------" <> line <> line <>
        ep                      <> line <> line <>
        owlpretty "} // verus!"    <> line <> line <>
        owlpretty "fn main() { entrypoint() }" <> line
      , lp                      <> line <> line <> line <> line <> 
        libCode
      )

extract :: TB.Env -> String -> TB.ModBody -> IO (Either ExtractionError (OwlDoc, OwlDoc))
extract tcEnv path modbody = runExtractionMonad tcEnv (initEnv path (modbody ^. TB.userFuncs)) $ extractModBody modbody
