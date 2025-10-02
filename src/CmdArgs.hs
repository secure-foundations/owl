{-# LANGUAGE TemplateHaskell #-}
module CmdArgs where

import Options.Applicative
import Data.Semigroup ((<>))
import qualified Data.Map.Strict as M
import Control.Lens
import System.Directory

data ExtractionMode = NoExtraction | ExtractOnlySpecs | ExtractAll
    deriving (Eq, Show)

data Flags = Flags { 
    _fDebug :: Maybe String,
    _fLogSMT :: Bool,
    _fCleanCache :: Bool,
    _fExtract :: ExtractionMode,
    _fDebugExtraction :: Bool,
    _fExtractBufOpt :: Bool,
    _fDoTests :: Bool,
    _fLax :: Bool,
    _fSkipRODisj :: Bool,
    _fFilePath :: String, 
    _fLocalTypeError :: Bool,
    _fLogTypecheck :: Bool,
    _fOnlyCheck :: Maybe String,
    _fFileContents :: String
                   }

makeLenses ''Flags

parseArgs :: Parser Flags
parseArgs = 
      Flags <$> 
      option (Just <$> str)
          ( long "debug" <> short 'd' <> help "Log debugging messages to file" <> value Nothing )
      <*>
          switch
          ( long "log-smt" <> short 'l' <> help "Log SMT queries" )
      <*>
          switch
          ( long "clean-smt-cache" <> short 'c' <> help "Clean SMT cache" )
      <*> extractionModeParser
      <*> switch
          ( long "debug-extraction" <> long "dbgext" <> help "Debug extraction" )
      <*> switch
          ( long "optimize-buffers" <> long "bufopt" <> help "Optimize buffer usage for extraction where possible" )
      <*>
          switch
          ( long "test" <> help "Do tests")
      <*>
          switch
          ( long "lax" <> help "Lax checking (skip some SMT queries)" )
      <*>
          switch
          ( long "skip-ro-disj" <> help "Skip RO disjointness queries" )
      <*> Options.Applicative.argument (str) (value "" <> metavar "FILE")
      <*>
          switch
          ( long "local-errors" <> help "Localize type errors to path condition" )
      <*>
          switch
          ( long "log-typecheck" <> help "Log typechecker progress" )
      <*> option (Just <$> str) (long "only-check" <> help "Only check the given function" <> value Nothing)
      <*> (pure "")
    where
        extractAllFlag = switch (long "extract" <> short 'e' <> help "Extract all specs and code")
        extractOnlySpecsFlag = switch (long "extract-only-specs" <> help "Extract only specs")
        extractionModeParser =
            (\ allFlag onlySpecsFlag -> case (allFlag, onlySpecsFlag) of
                                            (False, False) -> NoExtraction
                                            (True, False)  -> ExtractAll
                                            (False, True)  -> ExtractOnlySpecs
                                            (True, True)   -> error "Cannot specify both --extract and --extract-only-specs."
            ) <$> extractAllFlag <*> extractOnlySpecsFlag

doParseArgs :: IO Flags
doParseArgs = do 
    f <- execParser $ info (parseArgs <**> helper) (fullDesc <> progDesc "OWL")
    return $ postProcessFlags f

postProcessFlags :: Flags -> Flags
postProcessFlags f = 
    f { _fCleanCache = _fCleanCache f || _fLogSMT f || _fDoTests f }

getHelpMessage :: String
getHelpMessage = 
    case execParserPure defaultPrefs (info (parseArgs <**> helper) (fullDesc <> progDesc "OWL")) ["--help"] of
      Failure e -> fst (renderFailure e "")
      _ -> error "bad"

