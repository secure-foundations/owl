{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
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

type EM = ExtractionMonad VerusTy



genVerusDef :: CDef VerusTy -> EM VerusFunc
genVerusDef cdef = do
    throwError $ ErrSomethingFailed "TODO: genVerusDef"



genVerusStruct :: CStruct VerusTy -> EM (VerusStructDecl, Doc ann)
genVerusStruct (CStruct name fields) = do
    debugLog $ "genVerusStruct: " ++ name
    -- Lift all member fields to have the lifetime annotation of the whole struct
    let needsLifetime = any ((\t -> case t of RTOwlBuf l -> True; RTNamed (VN _ (Just _)) -> True; _ -> False) . snd) fields
    let lifetimeConst = "a"
    let verusFields = fmap (\(fname, fty) -> (cmpName fname, liftLifetime lifetimeConst fty)) fields
    let verusName = if needsLifetime then cmpNameLifetime name lifetimeConst else cmpName name
    let specname = (nl $ specName name)
    allLensValid <- genAllLensValid verusFields
    viewImpl <- genViewImpl verusName specname verusFields
    let sdecl = VerusStructDecl {
            rStructName = verusName,
            rStructFields = verusFields,
            rStructImplBlock = [allLensValid],
            rStructTraitImpls = [viewImpl]
        }
    return $ (sdecl, pretty "")
    where 
        liftLifetime a (RTOwlBuf _) = RTOwlBuf (Lifetime a)
        liftLifetime _ ty = ty

        genAllLensValid verusFields = do
            let genField (f, t) = case t of
                    RTOwlBuf _ -> Just $ RDotCall (RVar f) (nl "len_valid") []
                    RTNamed (VN _ (Just (Lifetime lt))) -> Just $ RDotCall (RVar f) (nl "len_valid") []
                    _ -> Nothing
            let lensValidFields = mapMaybe genField verusFields
            let body = if null lensValidFields then RBoolLit True else foldl1 (\a b -> RInfixOp a "&&" b) lensValidFields
            return $ VerusFunc {
                    rfName = nl "all_lens_valid",
                    rfMode = VOpenSpec,
                    rfExternalBody = False,
                    rfVerifierOpaque = False,
                    rfArgs = [],
                    rfRetTy = RTBool,
                    rfRequires = [],
                    rfEnsures = [],
                    rfBody = body
                }

        genViewImpl verusName specname verusFields = do
            let viewField (f, t) = 
                    let viewf = case t of
                            RTBool -> RDotCall (RFieldSel (RVar (nl "self")) f) (nl "dview") []
                            _ -> RDotCall (RDotCall (RFieldSel (RVar (nl "self")) f) (nl "dview") []) (nl "as_seq") []
                    in (nl (specNameOf f), viewf)
            let body = RStructLit specname $ map viewField verusFields
            let viewDef = VerusFunc {
                    rfName = nl "dview",
                    rfMode = VOpenSpec,
                    rfExternalBody = False,
                    rfVerifierOpaque = False,
                    rfArgs = [SelfArg RShared],
                    rfRetTy = RTNamed verusName,
                    rfRequires = [],
                    rfEnsures = [],
                    rfBody = body
                }
            let viewImpl = VerusTraitImpl {
                    rtiTraitName = cmpName "DView",
                    rtiForTy = RTNamed verusName,
                    rtiTraitTys = [VerusTyDecl (nl "V", RTNamed specname)],
                    rtiTraitFuncs = [viewDef]
                }
            return viewImpl
            


genVerusEnum :: CEnum VerusTy -> EM (VerusEnumDecl, Doc ann)
genVerusEnum (CEnum name cases) = do
    debugLog $ "genVerusEnum: " ++ name
    throwError $ ErrSomethingFailed "TODO: genVerusEnum"


-----------------------------------------------------------------------------
-- Utility functions
