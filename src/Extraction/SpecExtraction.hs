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
module SpecExtraction where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Except
import Control.Lens
import Prettyprinter
import Pretty
import Data.Type.Equality
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Unsafe
import Unbound.Generics.LocallyNameless.TH
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import ANFPass (isGhostTyAnn)
import Verus
import PrettyVerus
import ConcreteAST
import ExtractionBase
import AST
--import Data.String.Interpolate (i, __i, iii)
import Prettyprinter.Interpolate

type EM = ExtractionMonad FormatTy

seqU8 :: VerusTy
seqU8 = RTSeq RTU8

specTyOf :: FormatTy -> VerusTy
specTyOf FUnit = RTUnit
specTyOf FBool = RTBool
specTyOf FInt = RTVerusNat
specTyOf (FBuf _) = seqU8
specTyOf (FOption ft) = RTOption (specTyOf ft)
specTyOf (FStruct fn ffs) = RTStruct (specName fn) (fmap (\(n, t) -> (specName n, specTyOf t)) ffs)
specTyOf (FEnum n fcs) = RTEnum (specName n) (fmap (\(n, t) -> (specName n, fmap specTyOf t)) fcs)
specTyOf FGhost = RTVerusGhost

specTyOfSerialized :: FormatTy -> VerusTy
specTyOfSerialized (FStruct fn ffs) = seqU8
specTyOfSerialized (FEnum n fcs) = seqU8
specTyOfSerialized f = specTyOf f 

extractCTyDef :: CTyDef FormatTy -> EM (Doc ann)
extractCTyDef (CStructDef s) = extractCStruct s
extractCTyDef (CEnumDef e) = extractCEnum e

mkNestPattern :: [Doc ann] -> Doc ann
mkNestPattern l = 
        case l of
            [] -> pretty ""
            [x] -> x
            x:y:tl -> foldl (\acc v -> parens (acc <+> pretty "," <+> v)) (parens (x <> pretty "," <+> y)) tl 

extractCStruct :: CStruct FormatTy -> EM (Doc ann)
extractCStruct (CStruct n fs isVest) = do
    let rn = specName n
    let rfs = map (\(n, t) -> (specName n, specTyOf t)) fs
    let structFields = vsep $ fmap (\(n, t) -> [di|pub #{n}: #{pretty t},|]) rfs
    let structDef = [__di|
    pub struct #{rn} {
        #{structFields}
    }
    |]
    parseSerializeDefs <- if isVest then 
                                genParserSerializer (execName n) rn rfs 
                            else genParserSerializerNoVest (execName n) rn rfs
    constructor <- genConstructor n rn rfs
    return $ vsep [structDef, parseSerializeDefs, constructor]
    where
        genParserSerializer execname specname specfields = do
            let fieldNames = map (pretty . fst) $ specfields
            let fieldNamesCommaSep = hsep . punctuate comma $ fieldNames
            let fieldNamesNestPattern = mkNestPattern fieldNames
            let parse = [__di|
            \#[verifier::opaque]
            pub closed spec fn parse_#{specname}(x: Seq<u8>) -> Option<#{specname}> {
                let stream = parse_serialize::SpecStream { data: x, start: 0 };
                if let Ok((_,_,parsed)) = parse_serialize::spec_parse_#{execname}(stream) {
                    let (#{fieldNamesNestPattern}) = parsed;
                    Some(#{specname} { #{fieldNamesCommaSep} })
                } else {
                    None
                }
            }
            |]
            let fieldSels = map (\n -> [di|x.#{n}|]) fieldNames
            let fieldLens = map (\xn -> [di|#{xn}.len()|]) fieldSels
            let serInner = [__di|
            \#[verifier::opaque]
            pub closed spec fn serialize_#{specname}_inner(x: #{specname}) -> Option<Seq<u8>> {
                if no_usize_overflows_spec![ #{hsep . punctuate comma $ fieldLens} ] {
                    let stream = parse_serialize::SpecStream {
                        data: seq_u8_of_len(#{hsep . punctuate (pretty " + ") $ fieldLens}),
                        start: 0,
                    };
                    if let Ok((serialized, n)) = parse_serialize::spec_serialize_#{execname}(stream, (#{mkNestPattern fieldSels})) 
                    {
                        Some(seq_truncate(serialized.data, n))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            |]
            let ser = [__di|
            \#[verifier::opaque]
            pub closed spec fn serialize_#{specname}(x: #{specname}) -> Seq<u8> {
                if let Some(val) = serialize_#{specname}_inner(x) {
                    val
                } else {
                    seq![]
                }
            }
            |]
            let implOwlSpecSer = [__di|
            impl OwlSpecSerialize for #{specname} {
                open spec fn as_seq(self) -> Seq<u8> {
                    serialize_#{specname}(self)
                }
            }
            |]
            return $ vsep [parse, serInner, ser, implOwlSpecSer]

        genParserSerializerNoVest execname specname specfields = do
            let parse = [__di|
            \#[verifier::external_body]
            pub closed spec fn parse_#{specname}(x: Seq<u8>) -> Option<#{specname}> {
                // cant autogenerate vest parser
                todo!()
            }
            |]
            let ser = [__di|
            \#[verifier::external_body]
            pub closed spec fn serialize_#{specname}(x: #{specname}) -> Seq<u8> {
                // cant autogenerate vest serializer
                todo!()
            }
            |]
            let implOwlSpecSer = [__di|
            impl OwlSpecSerialize for #{specname} {
                open spec fn as_seq(self) -> Seq<u8> {
                    serialize_#{specname}(self)
                }
            }
            |]
            return $ vsep [parse, ser, implOwlSpecSer]


        genConstructor owlName specname specfields = do
            let fieldNames = map (pretty . fst) $ specfields
            let args = hsep . punctuate comma $ map (\(n,t) -> [di|arg_#{n}: #{pretty t}|]) specfields
            let mkFields = hsep . punctuate comma $ map (\(n,_) -> [di|#{n}: arg_#{n}|]) specfields
            let constructor = [__di|
            // TODO: make sure the arg types line up
            pub open spec fn #{owlName}(#{args}) -> #{specname} {
                #{specname} { 
                    #{mkFields} 
                }
            }
            |]
            return constructor


extractCEnum :: CEnum FormatTy -> EM (Doc ann)
extractCEnum (CEnum n cs isVest) = do
    let rn = specName n
    let rfs = map (\(n, t) -> (specName n, fmap specTyOf t)) $ M.assocs cs
    let rfsOwlNames = map (\(n, t) -> (n, fmap specTyOf t)) $ M.assocs cs
    let enumCases = vsep $ fmap (\(n, t) -> [di|#{n}(#{pretty t}),|]) rfs
    let enumDef = [__di|
    pub enum #{rn} {
        #{enumCases}
    }
    use crate::#{rn}::*;
    |]
    parseSerializeDefs <- genParserSerializer (execName n) rn rfs
    constructors <- genConstructors n rn rfsOwlNames
    enumTests <- genEnumTests n rn rfsOwlNames
    return $ vsep [enumDef, parseSerializeDefs, constructors, enumTests]
    where
        genParserSerializer execname specname speccases = do
            let parse = [__di|
            \#[verifier::external_body]
            pub closed spec fn parse_#{specname}(x: Seq<u8>) -> Option<#{specname}> {
                todo!()
            }
            |]
            let serInner = [__di|
            \#[verifier::external_body]
            pub closed spec fn serialize_#{specname}_inner(x: #{specname}) -> Option<Seq<u8>> {
                todo!()
            }
            |]
            let ser = [__di|
            \#[verifier::external_body]
            pub closed spec fn serialize_#{specname}(x: #{specname}) -> Seq<u8> {
                todo!()
            }
            |]
            let implOwlSpecSer = [__di|
            impl OwlSpecSerialize for #{specname} {
                open spec fn as_seq(self) -> Seq<u8> {
                    serialize_#{specname}(self)
                }
            }
            |]
            return $ vsep [parse, serInner, ser, implOwlSpecSer]

        genConstructors owlName specname speccases = do
            vsep <$> mapM (genConstructor owlName specname) speccases

        genConstructor owlName specname (caseName, Nothing) = do
            return [__di|
            pub open spec fn #{caseName}() -> #{specname} {
                crate::#{specname}::#{specName caseName}()
            }
            |]
        genConstructor owlName specname (caseName, Just caseTy) = do
            return [__di|
            pub open spec fn #{caseName}(x: #{pretty caseTy}) -> #{specname} {
                crate::#{specname}::#{specName caseName}(x)
            }
            |]
        
        genEnumTests owlName specname speccases = do
            tests <- mapM mkEnumTest speccases
            return $ vsep tests
            where
                mkEnumTest (caseName, topt) = do
                    let var = case topt of
                            Just t -> [di|_|]
                            Nothing -> [di||]
                    return [__di|
                    pub open spec fn #{caseName}_enumtest(x: #{specname}) -> bool {
                        match x {
                            #{specname}::#{specName caseName}(#{var}) => true,
                            _ => false,
                        }
                    }
                    |]


extractEndpoint :: Endpoint -> EM (Doc ann)
extractEndpoint (Endpoint evar) = return . pretty . replacePrimes . show $ evar
extractEndpoint (EndpointLocality (Locality s _)) = do
    l <- flattenPath s
    return $ pretty "Endpoint::Loc_" <> pretty l

extractVar :: CDataVar FormatTy -> EM (Doc ann)
extractVar n = do
    case name2String n of
        "_" -> pretty . show <$> fresh (string2Name "_unused")
        s -> return . pretty . replacePrimes $ s

specBuiltins :: M.Map String (String, [VerusTy], VerusTy)
specBuiltins = M.mapWithKey addSpecName builtins' where
    addSpecName n (args, rty) = (n, args, rty)
    builtins' = M.fromList [
          ("enc", ([seqU8, seqU8, seqU8], seqU8))
        , ("dec", ([seqU8, seqU8], RTOption seqU8))
        , ("sign", ([seqU8, seqU8], seqU8))
        , ("vrfy", ([seqU8, seqU8, seqU8], RTOption seqU8))
        , ("dhpk", ([seqU8], seqU8))
        , ("dh_combine", ([seqU8, seqU8], seqU8))
        , ("mac", ([seqU8, seqU8], seqU8))
        , ("mac_vrfy", ([seqU8, seqU8, seqU8], RTOption seqU8))
        , ("pkenc", ([seqU8, seqU8], seqU8))
        , ("pkdec", ([seqU8, seqU8], seqU8))
        -- , ("enc_st_aead", ([seqU8, seqU8, RTUsize, seqU8], seqU8)) -- special-cased
        , ("dec_st_aead", ([seqU8, seqU8, seqU8, seqU8], RTOption seqU8))
        , ("is_group_elem", ([seqU8], RTBool))
        , ("crh", ([seqU8], seqU8))
        , ("bytes_as_counter", ([seqU8], RTUsize))
        , ("counter_as_bytes", ([RTRef RShared RTUsize], seqU8))
        , ("kdf", ([RTUsize, seqU8, seqU8, seqU8], seqU8))
        ]
    -- diffNameBuiltins = M.fromList [
    --       ("kdf", ("extract_expand_to_len", [seqU8, seqU8, seqU8, seqU8], seqU8))
    --     ]

extractCAExpr :: CAExpr FormatTy -> EM (Doc ann)
extractCAExpr aexpr = do
    case aexpr ^. tval of
        CAVar s v -> extractVar v
        CAApp f args -> do
            case specBuiltins M.!? f of
                Just (f, argDstTys, rSrcTy) -> do
                    args' <- mapM extractCAExpr args
                    let argtys = map (^. tty) args
                    args'' <- zipWithM specCast (zip args' argtys) argDstTys
                    return [di|#{f}(#{hsep . punctuate comma $ args''})|]
                Nothing -> do
                    case f of
                        "unit" -> return [di|()|]
                        "andp" -> return [di|ghost_unit()|]
                        "true" -> return [di|true|]
                        "false" -> return [di|false|]
                        "Some" -> do
                            let [a] = args
                            a' <- extractCAExpr a
                            return [di|Option::Some(#{a'})|]
                        "None" -> return [di|Option::None|]
                        "eq" -> do
                            let [a,b] = args
                            a' <- extractCAExpr a
                            b' <- extractCAExpr b
                            return [di|#{a'} == #{b'}|]
                        "subrange" -> do
                            let [buf,start,end] = args
                            buf' <- extractCAExpr buf
                            start' <- extractCAExpr start
                            end' <- extractCAExpr end
                            return [di|Seq::subrange(#{buf'}, #{start'}, #{end'})|]
                        "enc_st_aead" -> do
                            let [key, msg, nonce, aad] = args
                            let extAndCast x dstty = do
                                    x' <- extractCAExpr x
                                    x'' <- specCast (x', x ^. tty) dstty
                                    return x''
                            key' <- extAndCast key seqU8
                            msg' <- extAndCast msg seqU8
                            nonce' <- extractCAExpr nonce
                            aad' <- extAndCast aad seqU8
                            return [di|enc_st_aead(#{key'}, #{msg'}, #{nonce'}, #{aad'})|]
                        _ | "?" `isSuffixOf` f -> do
                            -- Special case for enum test functions
                            let f' = init f ++ "_enumtest"
                            args' <- mapM extractCAExpr args
                            return [__di|
                            #{pretty f'}(#{hsep . punctuate comma $ args'})
                            |]
                        _ -> do
                            args' <- mapM extractCAExpr args
                            return [__di|
                                #{pretty f}(#{hsep . punctuate comma $ args'})
                            |]
        CAGet n -> do
            let rustN = execName n
            return [di|cfg.#{rustN}.view()|]
        CAGetVK n -> do
            let rustN = execName n
            return [di|cfg.pk_#{rustN}.view()|]
        (CAHexConst s) -> do
            bytelist <- hexStringToByteList s
            if null s then
                return $ pretty "empty_seq_u8()"
            else
                return $ pretty "seq![" <> bytelist <> pretty "]"
        CACounter ctrname -> return [di|#{execName ctrname}|]
        CAInt flen -> return . pretty . lowerFLen $ flen
        _ -> return [__di|
        /*
            TODO: SpecExtraction.extractCAExpr #{show aexpr}
        */
        |]

extractExpr :: CExpr FormatTy -> EM (Doc ann)
extractExpr expr = do
    case expr ^. tval of
        CSkip -> return [di|ret(())|]
        CRet ae -> do
            ae' <- extractCAExpr ae
            return [di|(ret(#{ae'}))|]
        CInput _ xek -> do
            let ((x, ev), k) = unsafeUnbind xek
            x' <- extractVar x
            let ev' = pretty . replacePrimes . show $ ev
            k' <- extractExpr k
            return [__di|
            (input(#{x'},#{ev'})) in 
            #{k'}
            |]
        COutput ae dst -> do
            dst' <- case dst of
                Just endp -> do
                    endp' <- extractEndpoint endp
                    return [di|(#{endp'})|]
                Nothing -> throwError OutputWithUnknownDestination
            ae' <- extractCAExpr ae
            ae'' <- specCast (ae', ae ^. tty) seqU8
            return [__di|
            (output (#{ae''}) to #{dst'})
            |]
        CSample fl ck -> do
            let sz = pretty $ lowerFLen fl
            let (coins, k) = unsafeUnbind ck
            coins' <- extractVar coins
            case k ^. tval of
                -- need special-case handling of CSample to insert the right itree syntax
                -- TODO: we could change the itree macro to handle sample more similarly to 
                -- input and output, but that would break backwards compatibility
                CRet (Typed t (CAApp "enc" [key, msg, coins])) -> do
                    key' <- extractCAExpr key
                    key'' <- specCast (key', key ^. tty) seqU8
                    msg' <- extractCAExpr msg
                    msg'' <- specCast (msg', msg ^. tty) seqU8
                    return [__di|
                    (sample(#{sz}, enc(#{key''}, #{msg''})))
                    |]
                _ -> throwError $ ErrSomethingFailed $ "Unsupported continuation after sample: " ++ show k
        CLet (Typed t (COutput a l)) _ xk -> do
            let (_, k) = unsafeUnbind xk
            o <- extractExpr (Typed t (COutput a l))
            k' <- extractExpr k
            return $ o <+> pretty "in" <> line <> k'
        CLet (Typed _ CSkip) _ xk -> do
            let (_, k) = unsafeUnbind xk
            extractExpr k
        CLet (Typed _ (CRet (Typed _ (CAApp "unit" _)))) _ xk -> do
            let (_, k) = unsafeUnbind xk
            extractExpr k
        CLet e _ xk -> do
            let (x, k) = unsafeUnbind xk
            case (name2String x, e ^. tval) of
                ("_", CRet (Typed _ (CAApp "unit" _))) -> do
                    extractExpr k
                (_, _) -> do
                    x' <- extractVar x
                    e' <- extractExpr e
                    k' <- extractExpr k
                    return $ pretty "let" <+> x' <+> pretty "=" <+> parens e' <+> pretty "in" <> line <> k'
        CBlock e -> extractExpr e
        CIf a e1 e2 -> do
            a' <- extractCAExpr a
            e1' <- extractExpr e1
            e2' <- extractExpr e2
            return $ parens $
                pretty "if" <+> parens a' <+> pretty "then" <+> parens e1' <+> pretty "else" <+> parens e2'
        CCase ae cases -> do
            ae' <- extractCAExpr ae
            translateCaseName <- case ae ^. tty of
                    FEnum n _ -> return specName
                    FOption _ -> return id
                    _ -> throwError $ TypeError "Unsupported spec case type"
            let extractCase (c, o) = do
                    case o of
                        Left e -> do
                            e' <- extractExpr e
                            let parens = case ae ^. tty of
                                    FOption _ -> ""
                                    _ -> "()"
                            return [__di|
                            | #{translateCaseName c}#{parens} => { 
                            #{e'} 
                            },
                            |]
                        Right xte -> do
                            let (x, (_, e)) = unsafeUnbind xte
                            x' <- extractVar x
                            e' <- extractExpr e
                            return [__di|
                            | #{translateCaseName c}(#{x'}) => {
                            #{e'}
                            },
                            |]
            cases' <- mapM extractCase cases
            return [__di|
            (case (#{ae'}) {
            #{vsep cases'}
            }
            )
            |]
        CParse pkind ae t maybeOtw xtsk -> do
            let (xts, k) = unsafeUnbind xtsk
            xs <- mapM (\(x,_,_) -> extractVar x) xts
            ae' <- extractCAExpr ae
            k' <- extractExpr k
            case t of
                FStruct n fs -> do
                    let dstTyName = specName n
                    let parsedTypeMembers = map (specName . fst) fs
                    let patfields = zipWith (\p x -> [di|#{p} : #{x}|]) parsedTypeMembers xs
                    (parseCall, badk) <- case maybeOtw of
                        Just otw -> do
                            let parseCall = [di|parse_#{dstTyName}(#{ae'})|]
                            otw' <- extractExpr otw
                            return (parseCall, [di|otherwise (#{otw'})|])
                        Nothing -> return (ae', [di||])
                    return $ parens [__di|
                    parse (#{parseCall}) as (#{dstTyName}{#{hsep . punctuate comma $ patfields}}) in {
                    #{k'}
                    } #{badk}
                    |]
                FEnum n cs -> throwError $ ErrSomethingFailed $ "TODO: spec enum parsing for " ++ show n
                FOption t' -> do
                    let [x] = xs
                    let PFromDatatype = pkind
                    return $ pretty "let" <+> x <+> pretty "=" <+> parens [di|(ret(#{ae'}))|] <+> pretty "in" <> line <> k'
                _ -> throwError $ TypeError $ "Unsupported spec parse type: " ++ show t
        CGetCtr ctrname -> do
            return $ parens $ pretty "ret" <> parens (pretty "counter_as_bytes" <> parens (pretty "mut_state." <> pretty (execName ctrname)))
        CCall f frty args -> do
            args' <- mapM extractCAExpr args
            let args'' = [di|cfg|] : [di|mut_state|] : args'
            return [di|(call(#{f}_spec(#{hsep . punctuate comma $ args''})))|]
        _ -> return [di|/* TODO: SpecExtraction.extractExpr #{show expr} */|]


extractDef :: LocalityName -> CDef FormatTy -> EM (Doc ann)
extractDef locName (CDef defname b) = do
    let specname = defname ++ "_spec"
    -- debugLog $ "Spec extracting def " ++ defname
    (owlArgs, (retTy, body)) <- unbindCDepBind b
    owlArgs' <- mapM extractArg owlArgs
    let specArgs = [di|cfg: cfg_#{locName}|] : [di|mut_state: state_#{locName}|] : owlArgs'
    -- NB: forces all data structures to be represented as Seq<u8> in spec
    let specRetTy = specTyOf retTy
    let itreeTy = [di|ITree<(#{pretty specRetTy}, state_#{locName}), Endpoint>|]
    (body, pureDef) <- case body of
        Just body -> do
            body' <- extractExpr body
            return (body', [di||])
        Nothing -> do
            let p = pureDef defname owlArgs' specRetTy
            let specArgVars = map (\(cdvar, strname, ty) -> pretty strname) owlArgs
            return ([di|(ret(#{defname}_pure(#{hsep . punctuate comma $ specArgVars})))|], p)
    return [__di|
        \#[verifier::opaque]
        pub open spec fn #{specname}(#{hsep . punctuate comma $ specArgs}) -> (res: #{itreeTy}) {
            owl_spec!(mut_state, state_#{locName},
                #{body}
            )
        }
        #{pureDef}
    |]
    where
        extractArg (cdvar, strname, ty) = do
            let specty = specTyOf ty
            return [di|#{pretty strname} : #{pretty specty}|]
        pureDef owlName specArgs specRt = 
            line <>
            pretty "#[verifier(external_body)] pub closed spec fn" <+> pretty owlName <> pretty "_pure" <> tupled specArgs <+> 
            pretty "->" <+> pretty specRt <+> line <> 
            braces (pretty "unimplemented!()" )

extractLoc :: (LocalityName, FormatLocalityData) -> EM (Doc ann)
extractLoc (locname, locdata) = do
    defs' <- mapM (extractDef locname) . catMaybes $ locdata ^. defs
    return $ vsep defs'


extractUserFunc :: CUserFunc FormatTy -> EM (Doc ann)
extractUserFunc (CUserFunc name b) = do
    let specname = name
    (args, (retTy, body)) <- unbindCDepBind b
    args' <- mapM extractArg args
    let specRetTy = specTyOf retTy
    body <- extractCAExpr body
    return [__di|
        \#[verifier::opaque]
        pub closed spec fn #{specname}(#{hsep . punctuate comma $ args'}) -> (res: #{pretty specRetTy}) {
            #{body}
        }
    |]
    where
        extractArg (cdvar, strname, ty) = do
            let specty = specTyOf ty
            return [di|#{pretty strname} : #{pretty specty}|]


specCast :: (Doc ann, FormatTy) -> VerusTy -> EM (Doc ann)
specCast (x, FStruct t _) (RTSeq RTU8) = return [di|serialize_#{specName t}(#{x})|]
specCast (x, FEnum t _) (RTSeq RTU8) = return [di|serialize_#{specName t}(#{x})|]
specCast (x, FOption (FStruct _ _)) (RTOption (RTSeq RTU8)) = return [di|option_as_seq(#{x})|]
specCast (x, FOption (FEnum _ _)) (RTOption (RTSeq RTU8)) = return [di|option_as_seq(#{x})|]
specCast (x, FInt) RTUsize = return [di|(#{x}) as usize|]
specCast (x, _) _ = return [di|#{x}|]