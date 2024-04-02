{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module ExtractionTop where
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
import CmdArgs
import ConcreteAST
import ExtractionBase
import qualified SMTBase
import qualified TypingBase as TB


extract :: Flags -> TB.Env SMTBase.SolverEnv -> String -> TB.ModBody -> IO (Either ExtractionError (OwlDoc, OwlDoc, OwlDoc))
extract flags tcEnv path modbody = runExtractionMonad tcEnv (initEnv flags path) $ extract' modbody



extract' :: TB.ModBody -> ExtractionMonad t (OwlDoc, OwlDoc, OwlDoc)
extract' modbody = do
    {-
    TODOS:
    1.  Split apart the modbody into its components (locality map, shared names, public keys, etc). This
        can reuse the preprocessing code from the bottom of Extraction.hs.old
    2.  concretify, which generates CDef FormatTy, CStruct FormatTy, CEnum FormatTy
    3.  lower to Rust types, using either `immut` or `opt`, generating CDef RustTy, CStruct RustTy, CEnum RustTy
    4.  emit Rust: RustAST types
    5.  just call owlpretty
    6.  harness generation
    -}
    throwError $ ErrSomethingFailed "TODO"

