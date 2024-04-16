{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module GenVerus where
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
--import Data.String.Interpolate (i, __i, iii)
import Prettyprinter.Interpolate

type EM = ExtractionMonad VerusTy



genVerusDef :: CDef VerusTy -> EM VerusFunc
genVerusDef cdef = do
    throwError $ ErrSomethingFailed "TODO: genVerusDef"


vestLayoutOf :: String -> VerusTy -> EM (Doc ann)
vestLayoutOf name (RTArray RTU8 len) = do
    lenConcrete <- concreteLength len
    return [di|#{name}: [u8; #{pretty lenConcrete}]|]
vestLayoutOf name t = throwError $ ErrSomethingFailed $ "TODO: vestLayoutOf" ++ show t

genVerusStruct :: CStruct VerusTy -> EM (Doc ann, Doc ann)
genVerusStruct (CStruct name fields) = do
    debugLog $ "genVerusStruct: " ++ name
    -- Lift all member fields to have the lifetime annotation of the whole struct
    let needsLifetime = any ((\t -> case t of RTOwlBuf _ -> True; RTWithLifetime _ _ -> True; _ -> False) . snd) fields
    let lifetimeConst = "a"
    let lifetimeAnnot = pretty $ if needsLifetime then "<'" ++ lifetimeConst ++ ">" else ""
    let verusFields = fmap (\(fname, fty) -> (fname, execName fname, liftLifetime lifetimeConst fty)) fields
    let verusName = execName name
    let specname = specName name
    let structTy = if needsLifetime then RTWithLifetime (RTNamed verusName) (Lifetime lifetimeConst) else RTNamed verusName
    let structFields = vsep . punctuate comma $ fmap (\(_, fname, fty) -> [di|pub #{fname}: #{pretty fty}|]) verusFields
    let structDef = [__di|
    pub struct #{verusName}#{lifetimeAnnot} {
        #{structFields}
    } 
    |]
    let emptyLifetimeAnnot = pretty $ if needsLifetime then "<'_>" else ""
    vestFormat <- genVestFormat verusName verusFields
    allLensValid <- genAllLensValid verusName verusFields emptyLifetimeAnnot
    viewImpl <- genViewImpl verusName specname verusFields emptyLifetimeAnnot
    parsleyWrappers <- genParsleyWrappers verusName specname structTy verusFields lifetimeConst
    return $ (vsep [structDef, allLensValid, viewImpl], vestFormat)
    where 
        liftLifetime a (RTOwlBuf _) = RTOwlBuf (Lifetime a)
        liftLifetime _ ty = ty

        genVestFormat name layoutFields = do
            let genField (_, f, l) = do 
                    layout <- vestLayoutOf f l
                    return [di|    #{layout},|]
            fields <- mapM genField layoutFields
            return [__di|
            #{name} = {
            #{vsep fields}
            }
            |]


        genAllLensValid :: VerusName -> [(String, VerusName, VerusTy)] -> Doc ann -> EM (Doc ann)
        genAllLensValid verusName fields lAnnot = do
            let fieldsValids = mapMaybe (\(_,fname, fty) -> 
                        case fty of 
                            RTWithLifetime (RTNamed _) (_) -> Just [di|self.#{fname}.len_valid()|]
                            RTOwlBuf _ -> Just [di|self.#{fname}.len_valid()|]
                            _ -> Nothing
                    ) fields
            let body = if null fieldsValids then [di|true|] else hsep . punctuate [di|&&|] $ fieldsValids
            return [__di|
            impl #{verusName}#{lAnnot} {
                pub open spec fn len_valid(&self) -> bool {
                    #{body}
                }
            }
            |]

        genViewImpl :: VerusName -> String -> [(String, VerusName, VerusTy)] -> Doc ann -> EM (Doc ann)
        genViewImpl verusName specname fields lAnnot = do
            let body = vsep . punctuate [di|,|] . fmap (\(fname, ename, _) -> [di|#{fname}: self.#{ename}.view()|]) $ fields
            return [__di|
            impl DView for #{verusName}#{lAnnot} {
                type V = #{specname};
                open spec fn dview(&self) -> #{specname} {
                    #{specname} { 
                        #{body}
                    }
                }
            }
            |]
        
        genParsleyWrappers :: VerusName -> String -> VerusTy -> [(String, VerusName, VerusTy)] -> String -> EM (Doc ann)
        genParsleyWrappers verusName specname structTy fields lifetimeConst = do
            let specParse = [di|parse_#{specname}|] 
            let execParse = [di|parse_#{verusName}|]
            let tupPatFields = tupled . fmap (\(_, fname, _) -> pretty fname) $ fields
            let mkField fname fty = do
                    mkf <- (pretty fname, u8slice) `cast` fty
                    return [di|#{fname}: #{mkf}|]
            mkStructFields <- tupled <$> mapM (\(_, fname, fty) -> mkField fname fty) fields
            let parse = [__di|
            pub exec fn #{execParse}<'#{lifetimeConst}>(arg: &'#{lifetimeConst} [u8]) -> (res: Option<#{pretty structTy}>) 
                // requires arg.len_valid()
                ensures
                    res is Some ==> #{specParse}(arg.dview()) is Some,
                    res is None ==> #{specParse}(arg.dview()) is None,
                    res matches Some(x) ==> x.dview() == #{specParse}(arg.dview())->Some_0,
                    res matches Some(x) ==> x.len_valid(),
            {
                reveal(#{specParse});
                let stream = parse_serialize::Stream { data: arg, start: 0 };
                if let Ok((_, _, parsed)) = parse_serialize::parse_owl_t(stream) {
                    let #{tupPatFields} = parsed;
                    Some (#{verusName} { #{mkStructFields} })
                } else {
                    None
                }
            }
            |]
            let specSer = [di|serialize_#{specname}|]
            let execSer = [di|serialize_#{verusName}|]
            let specSerInner = [di|serialize_#{specname}_inner|]
            let execSerInner = [di|serialize_#{verusName}_inner|]
            let lens = map (\(_, fname, _) -> [di|arg.#{fname}.len()|]) fields
            fieldsAsSlices <- tupled <$> mapM (\(_, fname, fty) -> (pretty fname, fty) `cast` u8slice) fields
            let ser = [__di|
            \#[verifier(external_body)] // to allow `as_mut_slice` call, TODO fix
            pub exec fn #{execSerInner}(arg: &#{verusName}) -> (res: Option<Vec<u8>>)
                requires arg.len_valid(),
                ensures
                    res is Some ==> #{specSerInner}(arg.dview()) is Some,
                    res is None ==> #{specSerInner}(arg.dview()) is None,
                    res matches Some(x) ==> x.dview() == #{specSerInner}(arg.dview())->Some_0,
            {
                reveal(#{specSerInner});
                if no_usize_overflows![ #{punctuate comma lens} ] {
                    let mut obuf = vec_u8_of_len(#{punctuate (pretty "+") lens});
                    let ser_result = parse_serialize::serialize_owl_t(obuf.as_mut_slice(), 0, (#{fieldsAsSlices}));
                    if let OK((_new_start, num_written)) = ser_result {
                        vec_truncate(&mut obuf, num_written);
                        Some(obuf)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            pub exec fn #{execSer}(arg: &#{verusName}) -> (res: Vec<u8>)
                requires arg.len_valid(),
                ensures  res.dview() == #{specSer}(arg.dview())
            {
                reveal(#{specSer});
                let res = #{execSerInner}(arg);
                assume(res is Some);
                res.unwrap();
            }
            |]
            return $ vsep [parse, ser]


genVerusEnum :: CEnum VerusTy -> EM (Doc ann, Doc ann)
genVerusEnum (CEnum name cases) = do
    debugLog $ "genVerusEnum: " ++ name
    return $ ([di||], [di||])
    -- throwError $ ErrSomethingFailed "TODO: genVerusEnum"


genVerusTyDef :: CTyDef VerusTy -> EM (Doc ann, Doc ann)
genVerusTyDef (CStructDef s) = genVerusStruct s
genVerusTyDef (CEnumDef e) = genVerusEnum e


genVerusTyDefs :: [(String, CTyDef VerusTy)] -> EM (Doc ann, Doc ann)
genVerusTyDefs tydefs = do
    debugLog "genVerusTyDefs"
    (tyDefs, vestDefs) <- unzip <$> mapM (genVerusTyDef . snd) tydefs
    return (vsep tyDefs, vsep vestDefs)


-----------------------------------------------------------------------------
-- Utility functions

-- castType v t1 t2 v returns an expression of type t2 whose contents are v, which is of type t1
cast :: (Doc ann, VerusTy) -> VerusTy -> EM (Doc ann)
cast (v, t1) t2 | t1 == t2 = return v
cast (v, t1) t2 | t2 == RTRef RShared t1 =
    return [di|&#{v}|]
cast (v, t1) t2 | t2 == RTRef RMut t1 =
    return [di|&mut #{v}|]    
cast (v, RTRef RMut t1) (RTRef RShared t2) | t1 == t2 =
    return [di|&#{v}|]
cast (v, RTVec t1) (RTRef b (RTSlice t2)) | t1 == t2 =
    return [di|&#{v}.as_slice()|]
cast (v, RTArray RTU8 _) (RTRef RShared (RTSlice RTU8)) =
    return [di|&#{v}.as_slice()|]
cast (v, RTRef _ (RTSlice RTU8)) (RTArray RTU8 _) =
    return [di|#{v}.try_into()|]
cast (v, t1) t2 = throwError $ CantCastType (show v) (show . pretty $ t1) (show . pretty $ t2)

u8slice :: VerusTy
u8slice = RTRef RShared (RTSlice RTU8)