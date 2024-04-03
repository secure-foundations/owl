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



genVerusStruct :: CStruct VerusTy -> EM VerusStructDecl
genVerusStruct (CStruct name fields) = do
    debugLog $ "genVerusStruct: " ++ name
    throwError $ ErrSomethingFailed "TODO: genVerusStruct"




genVerusEnum :: CEnum VerusTy -> EM VerusEnumDecl
genVerusEnum (CEnum name cases) = do
    debugLog $ "genVerusEnum: " ++ name
    throwError $ ErrSomethingFailed "TODO: genVerusEnum"


-----------------------------------------------------------------------------
-- Utility functions

cmpName :: String -> VerusName
cmpName owlName = VN ("owl_" ++ owlName) Nothing