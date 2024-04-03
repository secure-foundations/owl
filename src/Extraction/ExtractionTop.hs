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
import Rust
import qualified SMTBase
import qualified TypingBase as TB
import qualified Concretify
import qualified LowerImmut
import qualified GenRust


type LocalityName = String
type NameData = (String, FLen, Int) -- name, type, number of processID indices
type OwlDefData = (String, TB.Def)
data LocalityData nameData defData = LocalityData {
    _nLocIdxs :: Int, 
    _localNames :: [nameData], 
    _sharedNames :: [nameData], 
    _defs :: [defData], 
    _tables :: [(String, Ty)], 
    _counters :: [String]
}
makeLenses ''LocalityData
data ExtractionData defData tyData nameData = ExtractionData {
    _locMap :: M.Map LocalityName (LocalityData nameData defData),
    _presharedNames :: [nameData],
    _pubKeys :: [nameData],
    _tyDefs :: [tyData]
}
makeLenses ''ExtractionData

type OwlExtractionData = ExtractionData OwlDefData TB.TyDef NameData
type CFExtractionData = ExtractionData (CDef FormatTy) (CTyDef FormatTy) NameData
type CRExtractionData = ExtractionData (CDef RustTy) (CTyDef RustTy) NameData
type RustExtractionData = ExtractionData () () () -- TODO

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
    6.  Spec extraction (CDef FormatTy -> owl spec macro DSL (or just OwlDoc))
    7.  harness generation
    -}
    owlExtrData <- preprocessModBody modbody
    concreteExtrData <- concretifyPass owlExtrData
    specs <- specExtractPass concreteExtrData
    rustTyExtrData <- do
        fs <- use flags
        if fs ^. fExtractBufOpt then 
            throwError $ ErrSomethingFailed "TODO: buffer-optimization for extraction"
        else lowerImmutPass concreteExtrData
    (rustAst, extractedVest) <- genRustPass rustTyExtrData
    extractedOwl <- owlprettyPass rustAst
    (entryPoint, libHarness, callMain) <- mkEntryPoint rustTyExtrData
    p <- owlprettyFile "extraction/preamble.rs"
    lp <- owlprettyFile "extraction/lib_preamble.rs"
    -- userFuncs <- printCompiledUserFuncs
    return (
        p                       <> line <> line <> line <> line <> 
        owlpretty "verus! {"       <> line <> line <> 
        owlpretty "// ------------------------------------" <> line <>
        owlpretty "// ---------- SPECIFICATIONS ----------" <> line <>
        owlpretty "// ------------------------------------" <> line <> line <>
        specs                   <> line <> line <> line <> line <>
        owlpretty "// ------------------------------------" <> line <>
        owlpretty "// ---------- IMPLEMENTATIONS ---------" <> line <>
        owlpretty "// ------------------------------------" <> line <> line <>
        extractedOwl            <> line <> line <> line <> line <>
        owlpretty "// ------------------------------------" <> line <>
        owlpretty "// ------ USER-DEFINED FUNCTIONS ------" <> line <>
        owlpretty "// ------------------------------------" <> line <> line <>
        -- userFuncs               <> line <> line <>
        owlpretty "// ------------------------------------" <> line <>
        owlpretty "// ------------ ENTRY POINT -----------" <> line <>
        owlpretty "// ------------------------------------" <> line <> line <>
        entryPoint                 <> line <> line <>
        owlpretty "} // verus!"    <> line <> line <>
        callMain                <> line <> line
      , lp                      <> line <> line <> line <> line <> 
        libHarness
      , extractedVest
      )

preprocessModBody :: TB.ModBody -> ExtractionMonad t OwlExtractionData
preprocessModBody mb = do
    throwError $ ErrSomethingFailed "TODO preprocessModBody"

concretifyPass :: OwlExtractionData -> ExtractionMonad t CFExtractionData
concretifyPass owlExtrData = do
    throwError $ ErrSomethingFailed "TODO concretifyPass"

lowerImmutPass :: CFExtractionData -> ExtractionMonad t CRExtractionData
lowerImmutPass cfExtrData = do
    throwError $ ErrSomethingFailed "TODO lowerImmutPass"

-- OwlDoc is the vest file
genRustPass :: CRExtractionData -> ExtractionMonad t (RustExtractionData, OwlDoc)
genRustPass crExtrData = do
    throwError $ ErrSomethingFailed "TODO genRustPass"

owlprettyPass :: RustExtractionData -> ExtractionMonad t OwlDoc
owlprettyPass rustExtrData = do
    throwError $ ErrSomethingFailed "TODO owlprettyPass"

specExtractPass :: CFExtractionData -> ExtractionMonad t OwlDoc
specExtractPass cfExtrData = do
    throwError $ ErrSomethingFailed "TODO specExtractPass"

mkEntryPoint :: CRExtractionData -> ExtractionMonad t (OwlDoc, OwlDoc, OwlDoc)
mkEntryPoint rustExtrData = do
    fs <- use flags
    if fs ^. fExtractHarness then do
        throwError $ ErrSomethingFailed "TODO harness generation in mkEntryPoint"
    else 
        return (
                owlpretty "/* no entry point */"
            ,   owlpretty "fn main() { }" <> line
            ,   owlpretty "/* no library harness routines */"
        )
    throwError $ ErrSomethingFailed "TODO mkEntryPoint"


owlprettyFile :: String -> ExtractionMonad t OwlDoc
owlprettyFile fn = do
    s <- liftIO $ readFile fn
    return $ owlpretty s
