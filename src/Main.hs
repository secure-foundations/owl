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
import Test
import qualified Extraction as E

mkFlags :: String -> String -> String -> CmdArgs -> Flags
mkFlags contents path bname (CmdArgs d logsmt _ _ _) =
    Flags d logsmt path bname contents

main :: IO ()
main = do
  args <- doParseArgs
  if doTests args then doAllTests (mkFlags "" "" "" args) else do
      case fileName args of
        Nothing -> do
            putStrLn "Need input file!"
            putStrLn getHelpMessage
        Just fn -> do
          start <- getCPUTime
          s <- readFile fn
          case (P.parse parseFile (takeFileName fn) s) of
            Left err -> putStrLn $ "parse error: " ++ show err
            Right ast -> do
                do
                    res <- typeCheckDecls (mkFlags s (takeDirectory fn) (takeFileName fn) args) ast
                    case res of
                      Left _ -> return ()
                      Right () -> do
                          end <- getCPUTime
                          let diff = fromIntegral (end - start) / (10^12)
                          printf "Typechecking success! Time to typecheck: %0.5f seconds\n" (diff :: Double)
                          if extract args then do
                              let extfn = "extraction/src/main_impl.rs"
                              let specfn = "extraction/src/main.rs"
                              res <- E.extract (takeDirectory fn) ast
                              case res of
                                Left err -> E.printErr err
                                Right (rust_code, spec_code) -> do
                                  writeFile extfn $ "// Extracted rust code from file " ++ fn ++ ":\n"
                                  appendFile extfn $ show rust_code
                                  -- callProcess "rustfmt" [extfn]
                                  writeFile specfn $ "// Extracted Verus specs code from file " ++ fn ++ ":\n"
                                  appendFile specfn $ show spec_code
                                  -- callProcess "rustfmt" [specfn]
                                  putStrLn $ "Successfully extracted to file " ++ extfn ++ " and extracted Verus specs to file " ++ specfn
                                  return ()
                          else return ()
