module Test where
import Parse
import AST
import System.Environment
import Typing
import CmdArgs
import Control.Monad
import System.Directory
import System.Directory.Recursive
import System.FilePath
import Data.List
import Control.Lens
import qualified Text.Parsec as P
import Prettyprinter
import TypingBase

data TestType = ExpectSuccess | ExpectFailure 

doSingleTest :: String -> Flags -> TestType -> IO Bool
doSingleTest fileName f tt = do
    putStrLn $ "Testing " ++ fileName ++ "..."
    s <- readFile fileName
    pres <- P.runParserT parseFile () "" s
    case pres of
      Left perr -> do
          putStrLn $ show $ pretty "PARSE FAILURE: " <> pretty fileName <> pretty (show perr)
          return False
      Right ds -> do
        res <- typeCheckDecls f ds
        case (res, tt) of
          (Left err, ExpectSuccess) -> do
              putStrLn $ show $ pretty "TEST FAILURE: " <> pretty fileName <> pretty " expected to type check"
              return False
          (Left err, ExpectFailure) -> return True
          (Right _, ExpectSuccess) -> return True
          (Right _, ExpectFailure) -> do
              putStrLn $ show $ pretty "TEST FAILURE: " <> pretty fileName <> pretty " expected to fail, but type checking succeeded"
              return False

doAllTests :: Flags -> IO ()
doAllTests f = do
    let testDir = "./tests"
    let successDir = testDir </> "success"
    let failureDir = testDir </> "failure"
    toSucceed_ <- getFilesRecursive successDir
    toFail_ <- getFilesRecursive failureDir
    let toSucceed = filter (\s -> takeExtension s == ".owl" || takeExtension s == ".owli") toSucceed_
    let toFail = filter (\s -> takeExtension s == ".owl" || takeExtension s == ".owli") toFail_
    res1 <- forM toSucceed $ \s -> doSingleTest (s) (set fFilePath s f) ExpectSuccess
    res2 <- forM toFail $ \s -> doSingleTest (s) (set fFilePath s f) ExpectFailure
    let totalTests = length $ res1 ++ res2
    let failureTests = filter (\(b, _) -> not b) $ zip (res1 ++ res2) (toSucceed ++ toFail) 
    putStrLn $ "Result: " ++ show (totalTests - length failureTests) ++ " tests succeeded out of " ++ show totalTests ++ " total"
    when ((length failureTests) > 0) $ do
        putStrLn $ "Failed tests: " ++ intercalate ", " (map snd failureTests)
