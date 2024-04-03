{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
module Concretify where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Except
import Control.Lens
import Prettyprinter
import Pretty
import Data.Type.Equality
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Unsafe
import Unbound.Generics.LocallyNameless.TH
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import ANFPass (isGhostTyAnn)
import AST
import Rust
import ConcreteAST
import ExtractionBase
import qualified TypingBase as TB

type EM = ExtractionMonad FormatTy

concretifyTy :: Ty -> EM FormatTy
concretifyTy t = 
    case t^.val of
      TData _ _ _ -> return $ FBuf Nothing
      TDataWithLength _ a -> do
          a' <- liftCheck $ TB.resolveANF a
          case a'^.val of
            AEInt i -> return $ FBuf $ Just $ FLConst i 
            AELenConst s -> return $ FBuf $ Just $ FLNamed s
            _ -> throwError $ ErrSomethingFailed $ "Unsupported length annotation: " ++ show (owlpretty a')
      TGhost -> return $ FGhost
      TRefined t0 _ _ -> concretifyTy t0
      TOption t0 -> do
          ct <- concretifyTy t0
          return $ FOption ct
      TCase _ t1 t2 -> do
          ct1 <- concretifyTy t1
          ct2 <- concretifyTy t2
          unifyFormatTy ct1 ct2
      TConst ps _ -> error "unimp: need to look up"
      TBool _ -> return $ FBool
      TUnit -> return $ FUnit
      TName ne -> error "unimp"
      TVK ne -> error "unimp"
      TEnc_PK ne -> error "unimp"
      TSS ne1 ne2 -> error "unimp"
      TAdmit -> throwError $ ErrSomethingFailed "Got admit type during concretization"
      TExistsIdx _ it -> do
          (i, t) <- unbind it
          concretifyTy t -- TODO keep track of indices?
      THexConst s -> return $ hexConstType s

hexConstType :: String -> FormatTy
hexConstType s = error "unimp"

unifyFormatTy :: FormatTy -> FormatTy -> EM FormatTy
unifyFormatTy t1 t2 = error "unimp"

formatTyOfNameExp :: NameExp -> EM FormatTy
formatTyOfNameExp ne = error "unimp"

concretifyNameExpLoc :: NameExp -> EM String -- Returns the flattened path
concretifyNameExpLoc n = error "unimp"

concretifyPath :: Path -> EM String
concretifyPath p = error "unimp"

concreteTyOfApp :: Path -> [FuncParam] -> [FormatTy] -> EM FormatTy
concreteTyOfApp p ps ts = error "unimp"

concretifyAExpr :: AExpr -> EM (CAExpr FormatTy)
concretifyAExpr a = 
    case a^.val of
      AEGet n -> do
          t <- formatTyOfNameExp n
          s <- concretifyNameExpLoc n
          return $ Typed t $ CAGet s
      AELenConst s -> return $ Typed FInt $ CAInt $ FLNamed s
      AEInt i ->  return $ Typed FInt $ CAInt $ FLConst i
      AEHex s -> return $ Typed (hexConstType s) $ CAHexConst s
      AEApp p ps aes -> do
          vs <- mapM concretifyAExpr aes
          s <- concretifyPath p
          t <- concreteTyOfApp p ps (map _tty vs)
          return $ Typed t $ CAApp s vs
      AEVar s x -> do
          ot <- lookupVar $ castName x
          case ot of
            Nothing -> error "Unknown var"
            Just ct -> return $ Typed ct $ CAVar s $ castName x
      _ -> error "unimp"


concretifyExpr :: Expr -> EM (CExpr FormatTy)
concretifyExpr e =
    case e^.val of
      ERet a -> do
        v <- concretifyAExpr a
        return $ Typed (_tty v) $ CRet v

withVars :: [(CDataVar t, t)] -> ExtractionMonad t a -> ExtractionMonad t a
withVars xs k = do
    s <- use varCtx
    varCtx %= mappend (M.fromList xs)
    res <- k
    varCtx .= s
    return res

castName :: Name a -> Name b
castName (Fn x y) = Fn x y
castName (Bn x y) = Bn x y


withDepBind :: (Alpha a, Alpha b) => DepBind a -> ([(CDataVar FormatTy, FormatTy)] -> a -> EM (Maybe b)) -> EM (Maybe (CDepBind FormatTy b))
withDepBind (DPDone x) k = do
    res <- k [] x
    case res of
      Nothing -> return Nothing
      Just v -> return $ Just $ CDPDone v
withDepBind (DPVar t s xd) k = do
    (x, d) <- unbind xd
    ct <- concretifyTy t
    ores <- withVars [(castName x, ct)] $ withDepBind d $ \args v -> k ((castName x, ct):args) v
    case ores of
      Nothing -> return Nothing
      Just res -> return $ Just $ CDPVar ct s (bind (castName x) res)

concretifyDef :: String -> TB.Def -> EM (Maybe (CDef FormatTy))
concretifyDef defName (TB.DefHeader _) = return Nothing
concretifyDef defName (TB.Def bd) = do
    let ((sids, pids), dspec) = unsafeUnbind bd
    when (length sids > 1) $ throwError $ DefWithTooManySids defName
    ores <- withDepBind (dspec^.TB.preReq_retTy_body) $ \xts (p, retT, oexpr) ->  do
        when (not $ p `aeq` pTrue) $ throwError $ ErrSomethingFailed "Attempting to extract def with nontrivial prerequisite"
        cretT <- concretifyTy retT
        case oexpr of
          Nothing -> return Nothing
          Just e -> do
              ce <- concretifyExpr e
              return $ Just (cretT, ce)
    case ores of
      Nothing -> return Nothing
      Just res -> return $ Just $ CDef defName res
    

