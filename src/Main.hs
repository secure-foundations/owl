module Main where
import Parse
import Data.IORef
import AST
import System.Environment
import Typing
import Control.Monad
import qualified Text.Parsec as P
import qualified Data.Map.Strict as M
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
import qualified ExtractionTop as ET
import qualified ExtractionBase as EB
import Control.Lens
import Control.Monad ( when ) 


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
            Left err -> do
              putStrLn $ "parse error: " ++ show err 
              exitFailure
            Right ast -> do
                do
                    res <- typeCheckDecls (set fFileContents s args) ast
                    case res of
                      Left _ -> exitFailure
                      Right tcEnv -> do
                          -- end <- getCPUTime
                          -- let diff = fromIntegral (end - start) / (10^12)
                          printf "Typechecking success!\n" -- Time to typecheck: %0.5f seconds\n" (diff :: Double)
                          when (args^.fLogSMT) $ do
                              z3Results <- readIORef $ tcEnv^.z3Results
                              reportZ3Results fn z3Results
                          when (args^.fExtract) $ do
                              let extfn = "extraction/src/lib.rs"
                              -- let libfn = "extraction/src/lib.rs"
                              modBody <- doFlattening tcEnv
                              res <- ET.extract args tcEnv (takeDirectory fn) modBody
                              case res of
                                Left err -> EB.printErr err >> exitFailure
                                Right rust_code -> do
                                  -- putStrLn $ show rust_code
                                  writeFile extfn $ "// Extracted verus code from file " ++ fn ++ ":\n"
                                  appendFile extfn $ show rust_code
                                  -- writeFile libfn $ "// Extracted rust library code from file " ++ fn ++ ":\n"
                                  -- appendFile libfn $ show lib_code
                                  putStrLn $ "Successfully extracted to file " ++ extfn
                                  return ()
                          


lookupDefault :: String -> M.Map String a -> a -> a
lookupDefault x xs df = case M.lookup x xs of
                      Just a -> a
                      Nothing -> df


reportZ3Results :: String -> Map String Z3Result -> IO ()
reportZ3Results fn rs = do
    createDirectoryIfMissing False ".z3log"
    let csvFileName = ".z3log/" ++ takeFileName fn ++ ".csv"
    let columns = ["rlimit-count", "time"] 
    let csvHeader = "filename,unsat" ++ (mconcat $ map (\c -> "," ++ c) columns) ++ "\n"
    csvContents <- forM rs $ \(f, r) -> do
        let cols = concat $ map (\c -> "," ++ lookupDefault c (_z3Stats r) "undefined") columns
        return $ takeFileName f ++ "," ++ show (_isUnsat r) ++ cols ++ "\n"
    putStrLn $ "Writing Z3 results to " ++ csvFileName 
    writeFile csvFileName $ csvHeader ++ mconcat csvContents

