{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
module GenRust where
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
import Rust
import ConcreteAST
import ExtractionBase

type EM = ExtractionMonad RustTy



genRustDef :: CDef RustTy -> EM RustFunc
genRustDef cdef = do
    throwError $ ErrSomethingFailed "TODO: genRustDef"



genRustStruct :: CStruct RustTy -> EM RustStructDecl
genRustStruct cstruct = do
    throwError $ ErrSomethingFailed "TODO: genRustStruct"




genRustEnum :: CEnum RustTy -> EM RustEnumDecl
genRustEnum cenum = do
    throwError $ ErrSomethingFailed "TODO: genRustEnum"