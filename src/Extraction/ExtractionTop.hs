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
import Verus
import qualified SMTBase
import qualified TypingBase as TB
import qualified Concretify
import qualified LowerImmut
import qualified GenVerus
import qualified SpecExtraction


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
type CRExtractionData = ExtractionData (CDef VerusTy) (CTyDef VerusTy) NameData
type VerusExtractionData = ExtractionData () () () -- TODO

extract :: Flags -> TB.Env SMTBase.SolverEnv -> String -> TB.ModBody -> IO (Either ExtractionError (Doc ann, Doc ann, Doc ann))
extract flags tcEnv path modbody = runExtractionMonad tcEnv (initEnv flags path) $ extract' modbody


extract' :: TB.ModBody -> ExtractionMonad t (Doc ann, Doc ann, Doc ann)
extract' modbody = do
    {-
    TODOS:
    1.  Split apart the modbody into its components (locality map, shared names, public keys, etc). This
        can reuse the preprocessing code from the bottom of Extraction.hs.old
    2.  concretify, which generates CDef FormatTy, CStruct FormatTy, CEnum FormatTy
    3.  lower to Verus types, using either `immut` or `opt`, generating CDef VerusTy, CStruct VerusTy, CEnum VerusTy
    4.  emit Verus: VerusAST types
    5.  just call pretty
    6.  Spec extraction (CDef FormatTy -> owl spec macro DSL (or just Doc ann))
    7.  harness generation
    -}
    owlExtrData <- preprocessModBody modbody
    concreteExtrData <- concretifyPass owlExtrData
    specs <- specExtractPass concreteExtrData
    verusTyExtrData <- do
        fs <- use flags
        if fs ^. fExtractBufOpt then 
            throwError $ ErrSomethingFailed "TODO: buffer-optimization for extraction"
        else lowerImmutPass concreteExtrData
    (verusAst, extractedVest) <- genVerusPass verusTyExtrData
    extractedOwl <- prettyPass verusAst
    (entryPoint, libHarness, callMain) <- mkEntryPoint verusTyExtrData
    p <- prettyFile "extraction/preamble.rs"
    lp <- prettyFile "extraction/lib_preamble.rs"
    -- userFuncs <- printCompiledUserFuncs
    return (
        p                       <> line <> line <> line <> line <> 
        pretty "verus! {"       <> line <> line <> 
        pretty "// ------------------------------------" <> line <>
        pretty "// ---------- SPECIFICATIONS ----------" <> line <>
        pretty "// ------------------------------------" <> line <> line <>
        specs                   <> line <> line <> line <> line <>
        pretty "// ------------------------------------" <> line <>
        pretty "// ---------- IMPLEMENTATIONS ---------" <> line <>
        pretty "// ------------------------------------" <> line <> line <>
        extractedOwl            <> line <> line <> line <> line <>
        pretty "// ------------------------------------" <> line <>
        pretty "// ------ USER-DEFINED FUNCTIONS ------" <> line <>
        pretty "// ------------------------------------" <> line <> line <>
        -- userFuncs               <> line <> line <>
        pretty "// ------------------------------------" <> line <>
        pretty "// ------------ ENTRY POINT -----------" <> line <>
        pretty "// ------------------------------------" <> line <> line <>
        entryPoint                 <> line <> line <>
        pretty "} // verus!"    <> line <> line <>
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

-- Doc ann is the vest file
genVerusPass :: CRExtractionData -> ExtractionMonad t (VerusExtractionData, Doc ann)
genVerusPass crExtrData = do
    throwError $ ErrSomethingFailed "TODO genVerusPass"

prettyPass :: VerusExtractionData -> ExtractionMonad t (Doc ann)
prettyPass verusExtrData = do
    throwError $ ErrSomethingFailed "TODO prettyPass"

specExtractPass :: CFExtractionData -> ExtractionMonad t (Doc ann)
specExtractPass cfExtrData = do
    throwError $ ErrSomethingFailed "TODO specExtractPass"

mkEntryPoint :: CRExtractionData -> ExtractionMonad t (Doc ann, Doc ann, Doc ann)
mkEntryPoint verusExtrData = do
    fs <- use flags
    if fs ^. fExtractHarness then do
        throwError $ ErrSomethingFailed "TODO harness generation in mkEntryPoint"
    else 
        return (
                pretty "/* no entry point */"
            ,   pretty "fn main() { }" <> line
            ,   pretty "/* no library harness routines */"
        )
    throwError $ ErrSomethingFailed "TODO mkEntryPoint"


prettyFile :: String -> ExtractionMonad t (Doc ann)
prettyFile fn = do
    s <- liftIO $ readFile fn
    return $ pretty s
