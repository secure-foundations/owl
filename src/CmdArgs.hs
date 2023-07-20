module CmdArgs where

import Options.Applicative
import Data.Semigroup ((<>))

data CmdArgs = CmdArgs
    { 
        debugFlag :: Bool,
        logSmt :: Bool,
        extract :: Bool,
        doTests :: Bool,
        laxCheck :: Bool,
        fileName :: Maybe String
    }
    deriving (Show)

parseArgs :: Parser CmdArgs
parseArgs = CmdArgs
      <$>
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
      <*> argument (Just <$> str) (value Nothing <> metavar "FILE")

doParseArgs :: IO CmdArgs
doParseArgs = execParser $ info (parseArgs <**> helper) (fullDesc <> progDesc "OWL")

getHelpMessage :: String
getHelpMessage = 
    case execParserPure defaultPrefs (info (parseArgs <**> helper) (fullDesc <> progDesc "OWL")) ["--help"] of
      Failure e -> fst (renderFailure e "")
      _ -> error "bad"
