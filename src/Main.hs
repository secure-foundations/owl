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
          pres <- P.runParserT parseFile () (takeFileName fn) s
          case pres of
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
                              modBody <- doFlattening tcEnv
                              res <- E.extract tcEnv (takeDirectory fn) modBody
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
