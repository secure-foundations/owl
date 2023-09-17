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
import System.Exit
import Text.Printf
import ModuleFlattening
import Test
import qualified Extraction as E
import qualified ExtractionBase as EB
import Control.Lens

main :: IO ()
main = do
  args <- doParseArgs
  if args^.fDoTests then doAllTests args else do
      case args^.fFilePath of
        "" -> do
            putStrLn "Need input file!"
            putStrLn getHelpMessage
        fn -> do
          -- start <- getCPUTime
          s <- readFile fn
          case (P.parse parseFile (takeFileName fn) s) of
            Left err -> putStrLn $ "parse error: " ++ show err
            Right ast -> do
                do
                    res <- typeCheckDecls (set fFileContents s args) ast
                    case res of
                      Left _ -> return ()
                      Right tcEnv -> do
                          -- end <- getCPUTime
                          -- let diff = fromIntegral (end - start) / (10^12)
                          printf "Typechecking success!\n" -- Time to typecheck: %0.5f seconds\n" (diff :: Double)
                          if args^.fExtract then do
                              let extfn = "extraction/src/main.rs"
                              let libfn = "extraction/src/lib.rs"
                              modBody <- doFlattening tcEnv
                              res <- E.extract tcEnv (takeDirectory fn) modBody
                              case res of
                                Left err -> EB.printErr err >> exitFailure
                                Right (rust_code, lib_code) -> do
                                  -- putStrLn $ show rust_code
                                  writeFile extfn $ "// Extracted verus code from file " ++ fn ++ ":\n"
                                  appendFile extfn $ show rust_code
                                  -- Temporarily use a different formatter since rustfmt 
                                  -- doesn't look inside of the verus! macro
                                  callProcess "genemichaels" [extfn]
                                  writeFile libfn $ "// Extracted rust library code from file " ++ fn ++ ":\n"
                                  appendFile libfn $ show lib_code
                                  callProcess "genemichaels" [libfn]
                                  putStrLn $ "Successfully extracted to file " ++ extfn
                                  return ()
                          else return ()
