module Main where
import Parse
import AST
import System.Environment
import Typing
import qualified Text.Parsec as P
import Prettyprinter
import TypingBase
import System.FilePath
import CmdArgs
import System.Directory
import System.Process
import System.CPUTime
import Text.Printf
import ModuleFlattening
import Test
import qualified Extraction as E
import Control.Lens

mkFlags :: String -> String -> String -> CmdArgs -> Flags
mkFlags contents path bname (CmdArgs d logsmt _ _ lax _) =
    Flags d logsmt path bname lax contents

typeCheckWith :: String -> IO Env
typeCheckWith fn = do
      s <- readFile fn
      case (P.parse parseFile (takeFileName fn) s) of
        Left err -> do
            putStrLn $ "parse error: " ++ show err
            error "Parse error"
        Right ast -> do
                res <- typeCheckDecls (mkFlags s (takeDirectory fn) (takeFileName fn) (CmdArgs False False False False False (Just fn))) ast
                case res of
                  Left e -> return e
                  Right e -> return e

main :: IO ()
main = do
  args <- doParseArgs
  if doTests args then doAllTests (mkFlags "" "" "" args) else do
      case fileName args of
        Nothing -> do
            putStrLn "Need input file!"
            putStrLn getHelpMessage
        Just fn -> do
          -- start <- getCPUTime
          s <- readFile fn
          case (P.parse parseFile (takeFileName fn) s) of
            Left err -> putStrLn $ "parse error: " ++ show err
            Right ast -> do
                do
                    res <- typeCheckDecls (mkFlags s (takeDirectory fn) (takeFileName fn) args) ast
                    case res of
                      Left _ -> return ()
                      Right tcEnv -> do
                          -- end <- getCPUTime
                          -- let diff = fromIntegral (end - start) / (10^12)
                          printf "Typechecking success!\n" -- Time to typecheck: %0.5f seconds\n" (diff :: Double)
                          if extract args then do
                              let extfn = "extraction/src/main.rs"
                              let modBody = doFlattening tcEnv
                              res <- E.extract (takeDirectory fn) modBody
                              case res of
                                Left err -> E.printErr err
                                Right rust_code -> do
                                  -- putStrLn $ show rust_code
                                  writeFile extfn $ "// Extracted rust code from file " ++ fn ++ ":\n"
                                  appendFile extfn $ show rust_code
                                  callProcess "rustfmt" [extfn]
                                  putStrLn $ "Successfully extracted to file " ++ extfn
                                  return ()
                          else return ()
