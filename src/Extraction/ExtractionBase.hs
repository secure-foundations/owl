{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module ExtractionBase where
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
import Pretty
import Data.Type.Equality
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name ( Name(Bn, Fn) )
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Unbound.Generics.LocallyNameless.TH
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import AST
import CmdArgs
import System.IO
import qualified TypingBase as TB
import qualified SMTBase as SMT
import ConcreteAST

newtype ExtractionMonad t a = ExtractionMonad (ReaderT (TB.Env SMT.SolverEnv) (StateT (Env t) (ExceptT ExtractionError IO)) a)
    deriving (Functor, Applicative, Monad, MonadState (Env t), MonadError ExtractionError, MonadIO, MonadReader (TB.Env SMT.SolverEnv))

runExtractionMonad :: (TB.Env SMT.SolverEnv) -> Env t -> ExtractionMonad t a -> IO (Either ExtractionError a)
runExtractionMonad tcEnv env (ExtractionMonad m) = runExceptT . evalStateT (runReaderT m tcEnv) $ env

liftCheck :: TB.Check' SMT.SolverEnv a -> ExtractionMonad t a
liftCheck c = do
    e <- ask
    o <- liftIO $ runExceptT $ runReaderT (TB.unCheck $ local (set TB.tcScope $ TB.TcGhost False) c) e
    case o of 
      Left s -> ExtractionMonad $ lift $ throwError $ ErrSomethingFailed $ "flattenPath error: " 
      Right i -> return i

data Env t = Env {
        _flags :: Flags
    ,   _path :: String
    ,   _freshCtr :: Integer
    ,   _varCtx :: M.Map (CDataVar t) t
}



-- TODO: these may not all be needed
data ExtractionError =
      CantLayoutType Ty
    | TypeError String
    | UndefinedSymbol String
    | OutputWithUnknownDestination
    | LocalityWithNoMain String
    | UnsupportedOracleReturnType String
    | UnsupportedNameExp NameExp
    | UnsupportedNameType NameType
    | UnsupportedDecl String
    | DefWithTooManySids String
    | NameWithTooManySids String
    | UnsupportedSharedIndices String
    | CouldntParseInclude String
    | OddLengthHexConst
    | PreimageInExec String
    | GhostInExec String
    | ErrSomethingFailed String

instance OwlPretty ExtractionError where
    owlpretty (CantLayoutType t) =
        owlpretty "Can't make a layout for type:" <+> owlpretty t
    owlpretty (TypeError s) =
        owlpretty "Type error during extraction:" <+> owlpretty s
    owlpretty (UndefinedSymbol s) =
        owlpretty "Undefined symbol: " <+> owlpretty s
    owlpretty OutputWithUnknownDestination =
        owlpretty "Found a call to `output` without a destination specified. For extraction, all outputs must have a destination locality specified."
    owlpretty (LocalityWithNoMain s) =
        owlpretty "Locality" <+> owlpretty s <+> owlpretty "does not have a defined main function. For extraction, there should be a defined entry point function that must not take arguments: def" <+> owlpretty s <> owlpretty "_main () @" <+> owlpretty s
    owlpretty (UnsupportedOracleReturnType s) =
        owlpretty "Oracle" <+> owlpretty s <+> owlpretty "does not return a supported oracle return type for extraction."
    owlpretty (UnsupportedNameExp ne) =
        owlpretty "Name expression" <+> owlpretty ne <+> owlpretty "is unsupported for extraction."
    owlpretty (UnsupportedNameType nt) =
        owlpretty "Name type" <+> owlpretty nt <+> owlpretty "is unsupported for extraction."
    owlpretty (UnsupportedDecl s) =
        owlpretty "Unsupported decl type for extraction:" <+> owlpretty s
    owlpretty (DefWithTooManySids s) =
        owlpretty "Owl procedure" <+> owlpretty s <+> owlpretty "has too many sessionID parameters. For extraction, each procedure can have at most one sessionID parameter"
    owlpretty (NameWithTooManySids s) =
        owlpretty "Owl name" <+> owlpretty s <+> owlpretty "has too many sessionID parameters. For extraction, each procedure can have at most one sessionID parameter"
    owlpretty (UnsupportedSharedIndices s) =
        owlpretty "Unsupported sharing of indexed name:" <+> owlpretty s
    owlpretty (CouldntParseInclude s) =
        owlpretty "Couldn't parse included file:" <+> owlpretty s
    owlpretty OddLengthHexConst =
        owlpretty "Found a hex constant with an odd length, which should not be allowed."
    owlpretty (PreimageInExec s) =
        owlpretty "Found a call to `preimage`, which is not allowed in exec code:" <+> owlpretty s
    owlpretty (GhostInExec s) =
        owlpretty "Found a ghost value in exec code:" <+> owlpretty s
    owlpretty (ErrSomethingFailed s) =
        owlpretty "Extraction failed with message:" <+> owlpretty s

makeLenses ''Env

lookupVar :: CDataVar t -> ExtractionMonad t (Maybe t)
lookupVar x = do
    s <- use varCtx
    return $ M.lookup x s

printErr :: ExtractionError -> IO ()
printErr e = print $ owlpretty "Extraction error:" <+> owlpretty e

debugPrint :: String -> ExtractionMonad t ()
debugPrint = liftIO . putStrLn

debugLog :: String -> ExtractionMonad t ()
debugLog s = do
    fs <- use flags
    when (fs ^. fDebugExtraction) $ debugPrint ("    " ++ s)

instance Fresh (ExtractionMonad t) where
    fresh (Fn s _) = do
        n <- use freshCtr
        freshCtr %= (+) 1
        return $ Fn s n
    fresh nm@(Bn {}) = return nm

initEnv :: Flags -> String -> Env t
initEnv flags path = Env flags path 0 M.empty

flattenResolvedPath :: ResolvedPath -> String
flattenResolvedPath PTop = ""
flattenResolvedPath (PDot PTop y) = y
flattenResolvedPath (PDot x y) = flattenResolvedPath x ++ "_" ++ y
flattenResolvedPath s = error $ "failed flattenResolvedPath on " ++ show s

tailPath :: Path -> ExtractionMonad t String
tailPath (PRes (PDot _ y)) = return y
tailPath p = throwError $ ErrSomethingFailed $ "couldn't do tailPath of path " ++ show p

flattenPath :: Path -> ExtractionMonad t String
flattenPath (PRes rp) = do
    rp' <- liftCheck $ TB.normResolvedPath rp
    return $ flattenResolvedPath rp'
flattenPath p = error $ "bad path: " ++ show p