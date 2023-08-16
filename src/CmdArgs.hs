{-# LANGUAGE TemplateHaskell #-} 
module CmdArgs where

import Options.Applicative
import Data.Semigroup ((<>))
import qualified Data.Map.Strict as M
import Control.Lens
import System.Directory

data Flags = Flags { 
    _fDebug :: Bool,
    _fLogSMT :: Bool,
    _fExtract :: Bool,
    _fDoTests :: Bool,
    _fLax :: Bool,
    _fFilePath :: String, 
    _fLogTypecheck :: Bool,
    _fOnlyCheck :: Maybe String,
    _fFileContents :: String
                   }

makeLenses ''Flags

parseArgs :: Parser Flags
parseArgs = 
      Flags <$> 
          switch
          ( long "debug" <> short 'd' <> help "Print debugging messages" )
      <*>
          switch
          ( long "log-smt" <> short 'l' <> help "Log SMT queries" )
      <*>
          switch 
          ( long "extract" <> short 'e' <> 
            help "Extract rust code (requires rustfmt to be installed)" )
      <*>
          switch
          ( long "test" <> help "Do tests")
      <*>
          switch
          ( long "lax" <> help "Lax checking (skip some SMT queries)" )
      <*> Options.Applicative.argument (str) (value "" <> metavar "FILE")
      <*>
          switch
          ( long "log-typecheck" <> help "Log typechecker progress" )
      <*> option (Just <$> str) (long "only-check" <> help "Only check the given function" <> value Nothing)
      <*> (pure "")

doParseArgs :: IO Flags
doParseArgs = execParser $ info (parseArgs <**> helper) (fullDesc <> progDesc "OWL")

getHelpMessage :: String
getHelpMessage = 
    case execParserPure defaultPrefs (info (parseArgs <**> helper) (fullDesc <> progDesc "OWL")) ["--help"] of
      Failure e -> fst (renderFailure e "")
      _ -> error "bad"
