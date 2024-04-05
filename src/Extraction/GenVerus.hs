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
import ConcreteAST
import ExtractionBase
--import Data.String.Interpolate (i, __i, iii)
import Prettyprinter.Interpolate

type EM = ExtractionMonad VerusTy


-----------------------------------------------------------------------------
--- OLD: attempt at using AST types


genVerusDef :: CDef VerusTy -> EM VerusFunc
genVerusDef cdef = do
    throwError $ ErrSomethingFailed "TODO: genVerusDef"



genVerusStruct :: CStruct VerusTy -> EM (Doc ann, Doc ann)
genVerusStruct (CStruct name fields) = do
    debugLog $ "genVerusStruct: " ++ name
    -- Lift all member fields to have the lifetime annotation of the whole struct
    let needsLifetime = any ((\t -> case t of RTOwlBuf _ -> True; RTWithLifetime _ _ -> True; _ -> False) . snd) fields
    let lifetimeConst = "a"
    let verusFields = fmap (\(fname, fty) -> (fname, execName fname, liftLifetime lifetimeConst fty)) fields
    let verusName = execName name
    let specname = specName name
    let structFields = vsep $ fmap (\(_, fname, fty) -> [di|pub #{fname}: #{fty}|]) verusFields
    let structDef = [__di|
    pub struct #{verusName}#{if needsLifetime then "<'a>" else ""} {
        #{structFields}
    } 
    |]
    allLensValid <- genAllLensValid verusName verusFields
    viewImpl <- genViewImpl verusName specname verusFields
    return $ (vsep [structDef, allLensValid, viewImpl], pretty "")
    where 
        liftLifetime a (RTOwlBuf _) = RTOwlBuf (Lifetime a)
        liftLifetime _ ty = ty

        genAllLensValid :: String -> [(String, VerusName, VerusTy)] -> EM (Doc ann)
        genAllLensValid verusName fields = do
            let body = hsep . punctuate [di|&&|] . fmap (\(_,fname, _) -> [di|self.#{fname}.len_valid()|]) $ fields
            return [__di|
            impl #{verusName}<'_> {
                pub open spec fn len_valid(&self) -> bool {
                    #{body}
                }
            }
            |]

        genViewImpl :: String -> String -> [(String, VerusName, VerusTy)] -> EM (Doc ann)
        genViewImpl verusName specname fields = do
            let body = vsep . punctuate [di|,|] . fmap (\(fname, ename, _) -> [di|#{fname}: self.#{ename}.view()|]) $ fields
            return [__di|
            impl DView for #{verusName}<'_> {
                type V = #{specname};
                open spec fn view(&self) -> #{specname} {
                    #{specname} { 
                        #{body}
                    }
                }
            }
            |]
        
        -- genParsleyWrappers :: String -> [(String, VerusTy)] -> EM (Doc ann)



genVerusEnum :: CEnum VerusTy -> EM (VerusEnumDecl, Doc ann)
genVerusEnum (CEnum name cases) = do
    debugLog $ "genVerusEnum: " ++ name
    throwError $ ErrSomethingFailed "TODO: genVerusEnum"


-----------------------------------------------------------------------------
-- Utility functions
