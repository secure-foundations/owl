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
      TConst pth@(PRes (PDot p s)) _ -> do
          pthName <- concretifyPath pth
          md <- liftCheck $ TB.openModule p
          case lookup s (TB._tyDefs md) of
            Nothing -> error "Unknown type constant"
            Just (TB.TyAbstract) -> error "Concretize on abstract def"
            Just (TB.TyAbbrev t) -> concretifyTy t
            Just (TB.EnumDef bnd) -> do
                (_, ts) <- unbind bnd
                cs <- forM ts $ \(s, ot) -> do
                    cot <- traverse concretifyTy ot
                    return (s, cot)
                return $ FEnum pthName cs
            Just (TB.StructDef bnd) -> do
                (_, dp') <- unbind bnd
                let go dp = case dp of
                              DPDone _ -> return []
                              DPVar t s xres -> do
                                  c <- concretifyTy t
                                  (_, k) <- unbind xres
                                  ck <- go k
                                  return $ (s, c) : ck
                s <- go dp'
                return $ FStruct pthName s
      TBool _ -> return $ FBool
      TUnit -> return $ FUnit
      TName ne -> formatTyOfNameExp ne
      TVK ne -> error "unimp"
      TEnc_PK ne -> error "unimp"
      TSS ne1 ne2 -> return $ FBuf $ Just $ FLNamed "group" -- maybe we want internal repr here?
      TAdmit -> throwError $ ErrSomethingFailed "Got admit type during concretization"
      TExistsIdx _ it -> do
          (i, t) <- unbind it
          concretifyTy t -- TODO keep track of indices?
      THexConst s -> return $ hexConstType s

hexConstType :: String -> FormatTy
hexConstType s = FBuf $ Just $ FLConst $ length s `div` 2

unifyFormatTy :: FormatTy -> FormatTy -> EM FormatTy
unifyFormatTy t1 t2 = error "unimp"

formatTyOfNameExp :: NameExp -> EM FormatTy
formatTyOfNameExp ne = do
    nt <- liftCheck $ TB.getNameType ne 
    nk <- liftCheck $ TB.getNameKind nt
    return $ FBuf $ Just $ FLNamed $ 
        case nk of
          NK_KDF -> "kdfkey"
          NK_DH -> "exponent"
          NK_Enc -> "enckey"
          NK_PKE -> "pkekey"
          NK_Sig -> "sigkey"
          NK_MAC -> "mackey"
          NK_Nonce s -> s

concretifyNameExpLoc :: NameExp -> EM String -- Returns the flattened path
concretifyNameExpLoc n = error "unimp"

concretifyPath :: Path -> EM String
concretifyPath (PRes rp) = do
    rp' <- liftCheck $ TB.normResolvedPath rp
    return $ go rp'
        where
            go PTop = ""
            go (PDot PTop y) = y
            go (PDot x y) = go x ++ "_" ++ y
            go _ = error "Unhandled case in concretifyPath"
concretifyPath _ = error "Unhandled case in concretifyPath"

concreteTyOfApp :: Path -> [FuncParam] -> [FormatTy] -> EM FormatTy
concreteTyOfApp p ps ts = error "unimp"

-- () in ghost
ghostUnit :: CAExpr FormatTy
ghostUnit = Typed FGhost $ CAApp "unit" []

-- none()
noneConcrete :: FormatTy -> CAExpr FormatTy
noneConcrete rett = Typed rett $ CAApp "None" [] 

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
      AEKDF _ _ _ _ _ -> return ghostUnit
      AEGetEncPK n -> do
          let encPKFormatTy = error "unimp" 
          s <- concretifyNameExpLoc n
          return $ Typed encPKFormatTy $ CAGetEncPK s
      AEGetVK n -> do
          let vkFormatTy = error "unimp" 
          s <- concretifyNameExpLoc n
          return $ Typed vkFormatTy $ CAGetVK s
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


concretifyExpr :: Expr -> EM (CExpr FormatTy)
concretifyExpr e =
    case e^.val of
      EInput _ xk -> do
          ((x, ep), k) <- unbind xk
          k' <- withVars [(castName x, FBuf Nothing)] $ concretifyExpr k
          return $ Typed (_tty k') $ CInput $ bind (castName x, ep) k'
      EOutput a op -> do
          c <- concretifyAExpr a
          return $ Typed FUnit $ COutput c op
      ERet a -> do
        v <- concretifyAExpr a
        return $ Typed (_tty v) $ CRet v
      ELet e1 _ oanf s xk -> do
          c1 <- concretifyExpr e1
          (x, k) <- unbind xk
          k' <- withVars [(castName x, _tty c1)] $ concretifyExpr k
          return $ Typed (_tty k') $ CLet c1 oanf $ bind (castName x) k'
      ELetGhost _ s xk -> do
          (x, k) <- unbind xk
          k' <- withVars [(castName x, FGhost)] $ concretifyExpr k
          return $ Typed (_tty k') $ CLet (Typed FGhost (CRet ghostUnit)) Nothing $ bind (castName x) k'
      EBlock e b -> do
          c <- concretifyExpr e
          return $ Typed (_tty c) $ CBlock c
      EUnpack a _ ixk -> do
          c <- concretifyAExpr a
          ((i, x), k) <- unbind ixk
          k' <- withVars [(castName x, _tty c)] $ concretifyExpr k
          return $ Typed (_tty k') $ CLet (Typed (_tty c) (CRet c)) Nothing $ bind (castName x) k'
      EChooseBV _ _ xe -> do
          (x, e) <- unbind xe
          e' <- withVars [(castName x, FGhost)] $ concretifyExpr e
          return $ Typed (_tty e') $ CLet (Typed FGhost $ CRet ghostUnit) Nothing $ bind (castName x) e'
      EChooseIdx _ _ ie -> do
          (i, e) <- unbind ie
          concretifyExpr e
      EIf a e1 e2 -> do
          ca <- concretifyAExpr a
          c1 <- concretifyExpr e1
          c2 <- concretifyExpr e2
          t <- unifyFormatTy (_tty c1) (_tty c2)
          return $ Typed t $ CIf ca c1 c2
      EForallBV _ _ -> return $ Typed FGhost $ CRet ghostUnit
      EForallIdx _ _ -> return $ Typed FGhost $ CRet ghostUnit
      EPackIdx _ e -> concretifyExpr e
      EGuard a e -> do
          ca <- concretifyAExpr a 
          ce <- concretifyExpr e
          return $ Typed (_tty ce) $ CIf ca ce (Typed (_tty ce) $ CRet (noneConcrete $ _tty ce))
      EGetCtr p _ -> do
          s <- concretifyPath p
          return $ Typed FInt $ CGetCtr s
      EIncCtr p _ -> do
          s <- concretifyPath p
          return $ Typed FInt $ CGetCtr s
      EDebug _ -> return $ Typed FGhost $ CRet ghostUnit
      EAssert _ -> return $ Typed FGhost $ CRet ghostUnit
      EAssume _ -> return $ Typed FGhost $ CRet ghostUnit
      EAdmit -> return $ Typed FGhost $ CRet ghostUnit
      ECrypt cop aes -> do
          cs <- mapM concretifyAExpr aes
          concretifyCryptOp cop cs
      ECall p _ aes -> do
          s <- concretifyPath p
          cs <- mapM concretifyAExpr aes
          t <- returnTyOfCall p cs
          return $ Typed t $ CCall s cs
      EParse a t_target otherwiseCase xsk -> error "unimp"
      ECase e otherwiseCase xsk -> error "unimp"
      EPCase _ _ _ e -> concretifyExpr e
      ECorrCaseNameOf _ _ e -> concretifyExpr e
      EFalseElim e _ -> concretifyExpr e
      ETLookup p a -> do
          c <- concretifyAExpr a
          t <- typeOfTable p
          s <- concretifyPath p
          return $ Typed t $ CTLookup s c
      ETWrite p a1 a2 -> do
          c1 <- concretifyAExpr a1
          c2 <- concretifyAExpr a2
          s <- concretifyPath p
          return $ Typed FUnit $ CTWrite s c1 c2

typeOfTable :: Path -> EM FormatTy
typeOfTable (PRes (PDot p n)) = do
    md <- liftCheck $ TB.openModule p
    case lookup n (TB._tableEnv md) of
      Nothing -> error "table not found"
      Just (t, _) -> concretifyTy t

returnTyOfCall :: Path -> [CAExpr FormatTy] -> EM FormatTy
returnTyOfCall p cs = do
    bfdef <- liftCheck $ TB.getDefSpec p
    ((bi1, bi2), dspec) <- unbind bfdef
    let (TB.DefSpec _ _ db) = dspec
    go db
        where
            go (DPDone (_, t, _)) = concretifyTy t
            go (DPVar _ _ xk) = do
                (_, k) <- unbind xk
                go k
      
concretifyCryptOp :: CryptOp -> [CAExpr FormatTy] -> EM (CExpr FormatTy)
concretifyCryptOp cop cs = error "unimp"

withVars :: [(CDataVar t, t)] -> ExtractionMonad t a -> ExtractionMonad t a
withVars xs k = do
    s <- use varCtx
    varCtx %= mappend (M.fromList xs)
    res <- k
    varCtx .= s
    return res



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
    

