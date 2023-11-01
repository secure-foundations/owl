{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module SpecExtraction where
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
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Name ( Name(Bn, Fn) )
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Unbound.Generics.LocallyNameless.TH
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import AST
import ConcreteAST
import System.IO
import qualified Text.Parsec as P
import qualified Parse as OwlP
import qualified TypingBase as TB
import ExtractionBase

----------------------------------------------------------------------------------
--- Datatype extraction

genParserSerializer :: String -> ExtractionMonad OwlDoc
genParserSerializer name = do
    -- TODO nesting design---Seq or ADT args---depends on parsing lib
    let parser = owlpretty "#[verifier(external_body)]" <+> owlpretty "pub closed spec fn parse_" <> owlpretty name <> parens (owlpretty "x: Seq<u8>") <+>
                    owlpretty "->" <+> owlpretty "Option" <> angles (owlpretty name) <+> braces (line <>
                    owlpretty "todo!()" <> line
                )
    let serializer = owlpretty "#[verifier(external_body)]" <+> owlpretty "pub closed spec fn serialize_" <> owlpretty name <> parens (owlpretty "x:" <+> owlpretty name) <+>
                    owlpretty "->" <+> owlpretty "Seq<u8>" <+> braces (line <>
                    owlpretty "todo!()" <> line
                )
    return $ vsep [parser, serializer]

extractStruct :: String -> [(String, Ty)] -> ExtractionMonad OwlDoc
extractStruct owlName owlFields = do
    let name = specName owlName
    fields <- mapM (\(n, t) -> (rustifySpecTy . doConcretifyTy) t >>= \t' -> return (n, t')) owlFields
    let structDef = owlpretty "pub struct" <+> owlpretty name <> braces (line <> (
                        vsep . punctuate comma . map (\(n, t) -> owlpretty "pub" <+> owlpretty (specName n) <+> owlpretty ":" <+> owlpretty t) $ fields
                    ) <> line)
    parseSerializeDefs <- genParserSerializer name
    constructor <- genConstructor owlName fields
    selectors <- mapM (genFieldSelector owlName) fields
    return $ vsep $ [structDef, parseSerializeDefs, constructor] ++ selectors
    where
        genConstructor owlName fields = do
            specAdtFuncs %= S.insert owlName
            let args = parens . hsep . punctuate comma . map (\(n,_) -> owlpretty "arg_" <> owlpretty n <> owlpretty ": Seq<u8>") $ fields
            let body = owlpretty "serialize_" <> owlpretty (specName owlName) <>
                    parens (owlpretty (specName owlName) <> braces (hsep . punctuate comma . map (\(n,_) -> owlpretty (specName n) <> owlpretty ": arg_" <> owlpretty n) $ fields))
            return $
                owlpretty "pub open spec fn" <+> owlpretty owlName <> args <+> owlpretty "-> Seq<u8>" <+> braces (line <>
                    body
                <> line)
        genFieldSelector owlName (fieldName, fieldTy) = do
            specAdtFuncs %= S.insert fieldName
            return $
                owlpretty "pub open spec fn" <+> owlpretty fieldName <> parens (owlpretty "arg: Seq<u8>") <+> owlpretty "-> Seq<u8>" <+> braces (line <>
                    owlpretty "match" <+> owlpretty "parse_" <> owlpretty (specName owlName) <> parens (owlpretty "arg") <+> braces (line <>
                        owlpretty "Some(parsed) => parsed." <> owlpretty (specName fieldName) <> comma <> line <>
                        owlpretty "None => seq![] // TODO"
                    <> line)
                <> line)

extractEnum :: String -> [(String, Maybe Ty)] -> ExtractionMonad OwlDoc
extractEnum owlName owlCases = do
    let name = specName owlName
    cases <- mapM (\(n, topt) -> do
                        t' <- case topt of
                            Just t -> Just <$> (rustifySpecTy . doConcretifyTy) t
                            Nothing -> return Nothing
                        return (n, t')) owlCases
    let enumDef = owlpretty "#[is_variant]" <> line <> owlpretty "pub enum" <+> owlpretty name <> braces (line <> (
                        vsep . punctuate comma . map (\(n, t) -> owlpretty (specName n) <> parens (owlpretty t)) $ cases
                    ) <> line) <> line <> owlpretty "use crate::" <> owlpretty name <> owlpretty "::*;" <> line
    parseSerializeDefs <- genParserSerializer name
    caseConstructors <- mapM (genCaseConstructor name) cases
    return $ vsep $ [enumDef, parseSerializeDefs] ++ caseConstructors
    where
        genCaseConstructor name (caseName, Just caseTy) = do
            specAdtFuncs %= S.insert caseName
            return $
                owlpretty "pub open spec fn" <+> owlpretty caseName <> parens (owlpretty "x: Seq<u8>") <+> owlpretty "-> Seq<u8>" <+> braces (line <>
                    owlpretty "serialize_" <> owlpretty name <> parens (
                        owlpretty "crate::" <> owlpretty name <> owlpretty "::" <> owlpretty (specName caseName) <> parens (owlpretty "x")
                    )
                <> line)

        genCaseConstructor name (caseName, Nothing) = do
            specAdtFuncs %= S.insert caseName
            return $
                owlpretty "pub open spec fn" <+> owlpretty caseName <> owlpretty "()" <+> owlpretty "-> Seq<u8>" <+> braces (line <>
                    owlpretty "serialize_" <> owlpretty name <> parens (
                        owlpretty "crate::" <> owlpretty name <> owlpretty "::" <> owlpretty (specName caseName) <> owlpretty "()"
                    )
                <> line)


----------------------------------------------------------------------------------
--- Code generation

-- Owl builtin functions that must be printed differently in Rust
specBuiltinFuncs :: M.Map String ([OwlDoc] -> OwlDoc)
specBuiltinFuncs = M.fromList [
        ("unit", \_ -> owlpretty "()"),
        ("true", \_ -> owlpretty "true"),
        ("false", \_ -> owlpretty "false"),
        ("Some", \a -> owlpretty "Option::Some" <> tupled a),
        ("None", \_ -> owlpretty "Option::None"),
        ("eq", \[a1, a2] -> a1 <+> owlpretty "==" <+> a2),
        ("checknonce", \[a1, a2] -> a1 <+> owlpretty "==" <+> parens a2)
    ]

-- How to print len consts in spec land
specLenConsts :: M.Map String String
specLenConsts = M.fromList [
        -- ("signature", "256"),
        ("enckey", "KEY_SIZE()"),
        ("nonce", "NONCE_SIZE()"),
        -- ("mackey", hmacKeySize),
        -- ("maclen", hmacLen),
        -- ("pkekey", pkeKeySize),
        -- ("sigkey", sigKeySize),
        -- ("vk", vkSize),
        -- ("DH", dhSize),
        ("tag", "1")
    ]

extractEndpoint :: Endpoint -> ExtractionMonad OwlDoc
extractEndpoint (Endpoint evar) = return $ extractVar evar
extractEndpoint (EndpointLocality (Locality s _)) = do
    l <- flattenPath s
    return $ owlpretty "Endpoint::Loc_" <> owlpretty l

extractVar :: Name a -> OwlDoc
extractVar = owlpretty . replacePrimes . name2String

extractAExpr :: AExpr -> ExtractionMonad OwlDoc
extractAExpr ae = extractAExpr' (ae ^. val) where
    extractAExpr' (AEVar s n) = return $ extractVar n
    extractAExpr' (AEApp f _ as) = do
        as' <- mapM extractAExpr as
        ftail <- tailPath f
        case specBuiltinFuncs M.!? ftail of
            Just f' -> return $ f' as'
            Nothing  -> do
                -- Check if the func is a spec ADT func
                specAdtFs <- use specAdtFuncs
                if S.member ftail specAdtFs then do
                    return $ owlpretty ftail <> tupled as'
                else do
                    f' <- flattenPath f
                    return $ owlpretty f' <> tupled as'
        -- return $ owlpretty f' <> tupled as'
    extractAExpr' (AEHex s) = do
        bytelist <- hexStringToByteList s
        return $ owlpretty "seq![" <> bytelist <> owlpretty "]"
    extractAExpr' (AELenConst s) = do
        case specLenConsts M.!? s of
            Nothing -> throwError $ ErrSomethingFailed $ "TODO add spec len const " ++ s
            Just s' -> return $ owlpretty s'
    extractAExpr' (AEInt i) = return $ owlpretty i
    extractAExpr' (AEGet ne) = do
        ne' <- flattenNameExp ne
        return $ parens (owlpretty "*cfg." <> owlpretty ne') <> owlpretty ".view()"
    extractAExpr' (AEGetEncPK ne) = do
        ne' <- flattenNameExp ne
        return $ parens (owlpretty "*cfg.pk_" <> owlpretty ne') <> owlpretty ".view()"
    extractAExpr' (AEGetVK ne) = do
        ne' <- flattenNameExp ne
        return $ parens (owlpretty "*cfg.pk_" <> owlpretty ne') <> owlpretty ".view()"
    extractAExpr' (AEPackIdx s a) = extractAExpr a
    extractAExpr' (AEPreimage p _ _) = do
        p' <- flattenPath p
        throwError $ PreimageInExec p'

extractCryptOp :: CryptOp -> [AExpr] -> ExtractionMonad OwlDoc
extractCryptOp op owlArgs = do
    args <- mapM extractAExpr owlArgs
    case (op, args) of
        (CHash ((ropath,_,_):_) i, [x]) -> do
            roname <- flattenPath ropath
            orcls <- use oracles
            (outLen, sliceIdxs) <- case orcls M.!? roname of
                Nothing -> throwError $ TypeError $ "unrecognized random oracle " ++ roname
                Just p -> return p
            (start, end) <- case sliceIdxs M.!? i of
                Nothing -> throwError $ TypeError $ "bad index " ++ show i ++ " to random oracle " ++ roname
                Just p -> return p
            return $ 
                owlpretty "ret" <> parens 
                    (owlpretty "kdf" <> tupled [parens (printOrclLen outLen) <> owlpretty " as usize", x] <> owlpretty ".subrange" <> tupled [printOrclLen start, printOrclLen end])
        -- (CPRF s, _) -> do throwError $ ErrSomethingFailed $ "TODO implement crypto op: " ++ show op
        (CAEnc, [k, x]) -> do return $ owlpretty "sample" <> tupled [owlpretty "NONCE_SIZE()", owlpretty "enc" <> tupled [k, x]]
        (CADec, [k, x]) -> do return $ noSamp "dec" [k, x]
        (CEncStAEAD np _, [k, x, aad]) -> do
            n <- flattenPath np
            return $ noSamp "enc_st_aead" [k, x, owlpretty (rustifyName n), aad]
        (CDecStAEAD, [k, c, aad, n]) -> do return $ noSamp "dec_st_aead" [k, c, n, aad]
        (CPKEnc, [k, x]) -> do return $ noSamp "pkenc" [k, x]
        (CPKDec, [k, x]) -> do return $ noSamp "pkdec" [k, x]
        (CMac, [k, x]) -> do return $ noSamp "mac" [k, x]
        (CMacVrfy, [k, x, v]) -> do return $ noSamp "mac_vrfy" [k, x, v]
        (CSign, [k, x]) -> do return $ noSamp "sign" [k, x]
        (CSigVrfy, [k, x, v]) -> do return $ noSamp "vrfy" [k, x, v]
        (_, _) -> do throwError $ TypeError $ "got bad args for spec crypto op: " ++ show op ++ "(" ++ show args ++ ")"
    where
        noSamp name args = owlpretty "ret" <> parens (owlpretty name <> tupled args)
        printOrclLen = owlpretty . intercalate "+" . map (\x -> if x == "0" then "0" else specLenConsts M.! x) 

-- the Bool arg is whether the case has arguments
specCaseName :: Bool -> String -> String
specCaseName _ "Some" = "Some"
specCaseName _ "None" = "None"
specCaseName True c = specName c
specCaseName False c = specName c ++ "()"

extractExpr :: CExpr -> ExtractionMonad OwlDoc
extractExpr CSkip = return $ owlpretty "skip"
extractExpr (CInput xsk) = do
    let ((x, ev), sk) = unsafeUnbind xsk
    sk' <- extractExpr sk
    return $ parens (owlpretty "input" <+> tupled [extractVar x, extractVar ev]) <+> owlpretty "in" <> line <> sk'
extractExpr (COutput a l) = do
    a' <- extractAExpr a
    l' <- case l of
      Nothing -> throwError OutputWithUnknownDestination
      Just s  -> do
        s' <- extractEndpoint s
        return $ owlpretty "to" <+> parens s'
    return $ parens $ owlpretty "output " <> parens a' <+> l'
extractExpr (CLet (COutput a l) _ xk) = do
    let (_, k) = unsafeUnbind xk
    o <- extractExpr (COutput a l)
    k' <- extractExpr k
    return $ o <+> owlpretty "in" <> line <> k'
extractExpr (CLet CSkip _ xk) =
    let (_, k) = unsafeUnbind xk in extractExpr k
extractExpr (CLet e _ xk) = do
    let (x, k) = unsafeUnbind xk
    e' <- extractExpr e
    k' <- extractExpr k
    return $ owlpretty "let" <+> extractVar x <+> owlpretty "=" <+> parens e' <+> owlpretty "in" <> line <> k'
extractExpr (CIf a e1 e2) = do
    a' <- extractAExpr a
    e1' <- extractExpr e1
    e2' <- extractExpr e2
    return $ parens $
        owlpretty "if" <+> parens a' <+> owlpretty "then" <+> parens e1' <+> owlpretty "else" <+> parens e2'
extractExpr (CRet a) = do
    a' <- extractAExpr a
    return $ parens $ owlpretty "ret" <+> parens a'
extractExpr (CCall f is as) = do
    as' <- mapM extractAExpr as
    ftail <- flattenPath f
    return $ owlpretty "call" <> parens (owlpretty ftail <> owlpretty "_spec" <> tupled (owlpretty "cfg" : owlpretty "mut_state" : as'))
extractExpr (CCase a otk xs) = do
    debugPrint "TODO CCase parsing in spec extraction"
    a' <- extractAExpr a
    pcases <-
            mapM (\(c, o) ->
                case o of
                Left e -> do
                    e' <- extractExpr e
                    return $ owlpretty (specCaseName False c) <+> owlpretty "=>" <+> braces e' <> comma
                Right xe -> do
                    let (x, e) = unsafeUnbind xe
                    e' <- extractExpr e
                    return $ owlpretty (specCaseName True c) <+> parens (extractVar x) <+> owlpretty "=>" <+> braces e' <> comma
                ) xs
    return $ parens $ owlpretty "case" <+> parens a' <> line <> braces (vsep pcases)
extractExpr (CCrypt cop args) = do
    parens <$> extractCryptOp cop args
extractExpr (CIncCtr p ([], _)) = do
    p' <- flattenPath p
    return $ parens $ parens (owlpretty "inc_counter" <> tupled [owlpretty (rustifyName p')])
extractExpr (CGetCtr p ([], _)) = do
    p' <- flattenPath p
    return $ parens $ owlpretty "ret" <> parens (owlpretty "mut_state." <> owlpretty (rustifyName p'))
extractExpr (CParse a (CTConst p) (Just badk) bindpat) = do 
    t <- tailPath p
    let (pats, k) = unsafeUnbind bindpat
    fs <- lookupStruct . rustifyName $ t
    let patfields = zip (map (unignore . snd) pats) fs
    let printPat (v, (f, _)) = owlpretty (specName f) <+> owlpretty ":" <+> owlpretty v
    let patfields' = map printPat patfields
    a' <- extractAExpr a
    k' <- extractExpr k
    badk' <- extractExpr badk
    return $ parens $ owlpretty "parse" <+> parens (owlpretty "parse_" <> owlpretty (specName t) <> parens a') <+> owlpretty "as" <+> parens (owlpretty (specName t) <> (braces . hsep . punctuate comma) patfields') <+> owlpretty "in" <+> lbrace <> line <> k' <> line <> rbrace <+> owlpretty "otherwise" <+> parens badk'
extractExpr c = throwError . ErrSomethingFailed . show $ owlpretty "unimplemented case for Spec.extractExpr:" <+> owlpretty c
-- extractExpr (CTLookup n a) = return $ owlpretty "lookup" <> tupled [owlpretty n, extractAExpr a]
-- extractExpr (CTWrite n a a') = return $ owlpretty "write" <> tupled [owlpretty n, extractAExpr a, extractAExpr a']

specExtractArg :: (DataVar, Embed Ty) -> ExtractionMonad OwlDoc
specExtractArg (v, t) = do
    st <- rustifyArgTy . doConcretifyTy . unembed $ t
    return $ extractVar v <> owlpretty ":" <+> (owlpretty . specTyOf $ st)


extractDef :: String -> Locality -> CExpr -> [(DataVar, Embed Ty)] -> SpecTy -> ExtractionMonad OwlDoc
extractDef owlName (Locality lpath _) concreteBody owlArgs specRt = do
    lname <- flattenPath lpath
    specArgs <- mapM specExtractArg owlArgs
    let argsPrettied = hsep . punctuate comma $
            owlpretty "cfg:" <+> owlpretty (cfgName lname)
            : owlpretty "mut_state:" <+> owlpretty (stateName lname)
            : specArgs
    let rtPrettied = owlpretty "-> (res: ITree<(" <> owlpretty specRt <> comma <+> owlpretty (stateName lname) <> owlpretty "), Endpoint>" <> owlpretty ")"
    body <- extractExpr concreteBody
    return $ owlpretty "pub open spec fn" <+> owlpretty owlName <> owlpretty "_spec" <> parens argsPrettied <+> rtPrettied <+> lbrace <> line <>
        owlpretty "owl_spec!" <> parens (owlpretty "mut_state," <> owlpretty (stateName lname) <> comma <> line <>
            body
        <> line) <> line <>
        rbrace

mkSpecEndpoint :: [String] -> OwlDoc
mkSpecEndpoint lnames =
    owlpretty "#[is_variant]" <> line <> owlpretty "#[derive(Copy, Clone)]" <> line <>
    owlpretty "pub enum Endpoint" <+> braces (line <>
        (vsep . punctuate comma . map (\s -> owlpretty "Loc_" <> owlpretty s) $ lnames)
    <> line)

endpointOfAddr :: OwlDoc
endpointOfAddr = owlpretty "#[verifier(external_body)] pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint { unimplemented!() /* axiomatized */ }"