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


extractCTyDef :: CTyDef FormatTy -> EM (Doc ann)
extractCTyDef (CStructDef s) = extractCStruct s
extractCTyDef (CEnumDef e) = extractCEnum e

extractCStruct :: CStruct FormatTy -> EM (Doc ann)
extractCStruct (CStruct n fs) = do
    let rn = specName n
    let rfs = map (\(n, t) -> (specName n, specTyOf t)) fs
    let structFields = vsep $ fmap (\(n, t) -> [di|pub #{n}: #{pretty t},|]) rfs
    let structDef = [__di|
    pub struct #{rn} {
        #{structFields}
    }
    |]
    parseSerializeDefs <- genParserSerializer (execName n) rn rfs
    constructor <- genConstructor n rn rfs
    return $ vsep [structDef, parseSerializeDefs, constructor]
    where
        genParserSerializer execname specname specfields = do
            let fieldNames = map (pretty . fst) $ specfields
            let fieldNamesCommaSep = hsep . punctuate comma $ fieldNames
            let parse = [__di|
            \#[verifier::opaque]
            pub closed spec fn parse_#{specname}(x: Seq<u8>) -> Option<#{specname}> {
                let stream = parse_serialize::SpecStream { data: x, start: 0 };
                if let Ok((_,_,parsed)) = parse_serialize::spec_parse_#{execname}(stream) {
                    let (#{fieldNames}) = parsed;
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
                    if let Ok((serialized, n)) = parse_serialize::spec_serialize_#{execname}(stream, (#{tupled fieldSels})) 
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

        genConstructor owlName specname specfields = do
            let fieldNames = map (pretty . fst) $ specfields
            let args = hsep . punctuate comma $ map (\(n,t) -> [di|arg_#{n}: #{pretty t}|]) specfields
            let mkFields = hsep . punctuate comma $ map (\(n,_) -> [di|#{n}: arg_#{n}|]) specfields
            let constructor = [__di|
            // TODO: make sure the arg types line up
            pub open spec fn #{owlName}(#{args}) -> Seq<u8> {
                serialize_#{specname}(
                    #{specname} { 
                        #{mkFields} 
                    }
                )
            }
            |]
            return constructor

extractCEnum :: CEnum FormatTy -> EM (Doc ann)
extractCEnum (CEnum n cs) = do
    return [di|/* TODO extractCEnum #{n} */|]

