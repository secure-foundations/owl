{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
module LowerBufOpt where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List
import Data.Char
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
import ConcreteAST
import ExtractionBase
import Verus

type EM = ExtractionMonad FormatTy

lowerTy :: FormatTy -> EM VerusTy
lowerTy FUnit = return RTUnit
lowerTy FBool = return RTBool
lowerTy FInt = return RTUsize
lowerTy (FBuf Nothing) = return $ RTOwlBuf (Lifetime "_")
lowerTy (FBuf (Just flen)) = return $ RTOwlBuf (Lifetime "_")
lowerTy (FOption ft) = RTOption <$> lowerTy ft
lowerTy (FStruct fn ffs) = do
    let rn = execName fn
    rfs <- mapM (\(n, t) -> (,) (execName n) <$> lowerTy t) ffs
    return $ RTStruct rn rfs
lowerTy (FEnum n fcs) = do
    let rn = execName n
    rcs <- mapM (\(n, t) -> (,) (execName n) <$> mapM lowerTy t) fcs
    return $ RTEnum rn rcs
lowerTy FGhost = return $ RTVerusGhost
lowerTy FDummy = return $ RTDummy
lowerTy (FHexConst s) = return $ RTUnit

withVars :: [(CDataVar FormatTy, VerusTy)] -> EM a -> EM a
withVars xs k = do
    s <- use lowerCtx
    lowerCtx %= mappend (M.fromList xs)
    res <- k
    lowerCtx .= s
    return res

tyOf :: CDataVar FormatTy -> EM VerusTy
tyOf v = do
    ctx <- use lowerCtx
    case M.lookup v ctx of
        Just t -> return t
        Nothing -> throwError $ UndefinedSymbol $ "LowerBufOpt.tyOf: " ++ show v

mkApp :: String -> FormatTy -> [CAExpr VerusTy] -> EM (CAExpr VerusTy)
mkApp f frty argrtys = do
    case (f, frty) of
        ("enc_st_aead", _) -> do 
            let frty = RTStAeadBuilder
            return $ Typed frty $ CAApp "enc_st_aead_builder" argrtys
        (f, FStruct f' fields) | f == f' -> do
            let argtys = map (^. tty) argrtys
            if RTStAeadBuilder `elem` argtys then do
                debugPrint $ "mkApp struct constructor: " ++ f
                {-
                TODO: 
                - Have a way to "suspend" computations which floats up to the enclosing let-binding,
                  so that the code is emitted immediately prior to when it is used. (Can borrow from GenVerus)
                - In the lowerCtx, store some data structure for the suspended computation, which should contain
                  the way to construct the combinator, the way to construct the input to the combinator, and the
                  call to just construct the struct as normal. This will need to float up to the enclosing let-binding.
                - When we encounter a use of whatever variable was bound to this call, we examine its type to determine
                  whether it is being used as a struct or as a serialized buffer. If buffer, we emit the right serializing
                  call; if constructor, we just emit the constructor.
                - It is then easy to emit the optimization for `Output` as well.
                -}
                frty' <- lowerTy frty
                return $ Typed frty' $ CAApp f argrtys 
            else do
                frty' <- lowerTy frty
                return $ Typed frty' $ CAApp f argrtys 
        _ -> do
            frty' <- lowerTy frty
            return $ Typed frty' $ CAApp f argrtys

lowerCAExpr :: CAExpr FormatTy -> EM (CAExpr VerusTy)
lowerCAExpr aexpr = do
    rt <- lowerTy $ aexpr ^. tty
    let withRt x = return $ Typed rt x :: EM (CAExpr VerusTy)
    case aexpr ^. tval of
        CAVar s n -> do
            rtFromCtx <- tyOf n
            return $ Typed rtFromCtx $ CAVar s (castName n)
        CAApp f args -> do
            args' <- mapM lowerCAExpr args
            mkApp f (aexpr ^. tty) args'
        CAGet s -> withRt $ CAGet s
        CAGetEncPK s -> withRt $ CAGetEncPK s
        CAGetVK s -> withRt $ CAGetVK s
        CAInt fl -> withRt $ CAInt fl
        CAHexConst s -> withRt $ CAHexConst s
        CACounter s -> withRt $ CACounter s



lowerExpr :: CExpr FormatTy -> EM (CExpr VerusTy)
lowerExpr expr = do
    rt <- lowerTy $ expr ^. tty
    let withRt x = return $ Typed rt x :: EM (CExpr VerusTy)
    case expr ^. tval of
        CSkip -> withRt CSkip
        CRet ae -> do
            ae' <- lowerCAExpr ae
            return $ Typed (ae' ^. tty) $ CRet ae'
        CInput ft xek -> do
            ((x, ev), k) <- unbind xek
            frt <- lowerTy ft
            k' <- withVars [(x, frt)] $ lowerExpr k
            let xek' = bind (castName x, ev) k'
            return $ Typed (k' ^. tty) $ CInput frt xek'
        COutput ae dst -> do
            ae' <- lowerCAExpr ae
            withRt $ COutput ae' dst
        CSample flen t xk -> do
            (x, k) <- unbind xk
            t' <- lowerTy t
            k' <- withVars [(x, t')] $ lowerExpr k
            let xk' = bind (castName x) k'
            return $ Typed (k' ^. tty) $ CSample flen t' xk'
        CLet e oanf xk -> do
            (x, k) <- unbind xk
            e' <- lowerExpr e
            k' <- withVars [(x, e' ^. tty)] $ lowerExpr k
            let xk' = bind (castName x) k'
            return $ Typed (k' ^. tty) $ CLet e' oanf xk'
        CBlock e -> do
            e' <- lowerExpr e
            return $ Typed (e' ^. tty) $ CBlock e'
        CIf ae e1 e2 -> do
            ae' <- lowerCAExpr ae
            e1' <- lowerExpr e1
            e2' <- lowerExpr e2
            withRt $ CIf ae' e1' e2'
        CCase ae cases -> do
            ae' <- lowerCAExpr ae
            cases' <- forM cases $ \(n, c) -> do
                case c of
                    Left k -> do
                        k' <- lowerExpr k
                        return (n, Left k')
                    Right xtk -> do
                        (x, (t, k)) <- unbind xtk
                        t' <- lowerTy t
                        k' <- withVars [(x, t')] $ lowerExpr k
                        return (n, Right $ bind (castName x) (t', k'))
            withRt $ CCase ae' cases'
        CCall fn frty args -> do
            frty' <- lowerTy frty
            args' <- mapM lowerCAExpr args
            return $ Typed frty' $ CCall fn frty' args'
        CParse pk ae dst_ty otw xtsk -> do
            (xts, k) <- unbind xtsk
            xts' <- mapM (\(n, s, t) -> do t' <- lowerTy t ; return (castName n, s, t')) xts
            let ctx = map (\(x, _, t) -> (castName x, t)) xts'
            ae' <- lowerCAExpr ae
            dst_ty' <- lowerTy dst_ty
            otw' <- traverse lowerExpr otw
            k' <- withVars ctx $ lowerExpr k
            let xtsk' = bind xts' k'
            return $ Typed (k' ^. tty) $ CParse pk ae' dst_ty' otw' xtsk'
        CTLookup s ae -> do
            ae' <- lowerCAExpr ae
            withRt $ CTLookup s ae'
        CTWrite s ae1 ae2 -> do
            ae1' <- lowerCAExpr ae1
            ae2' <- lowerCAExpr ae2
            withRt $ CTWrite s ae1' ae2'
        CGetCtr s -> do
            withRt $ CGetCtr s
        CIncCtr s -> do
            withRt $ CIncCtr s
        

lowerArg :: (CDataVar FormatTy, String, FormatTy) -> EM (CDataVar VerusTy, String, VerusTy)
lowerArg (n, s, t) = do
    t' <- lowerTy t
    return (castName n, s, t')



lowerDef :: CDef FormatTy -> EM (CDef VerusTy)
lowerDef (CDef name b) = do
    (args, (retTy, body)) <- unbindCDepBind b
    args' <- mapM lowerArg args
    retTy' <- lowerTy retTy
    let argctx = map (\(v,_,t) -> (castName v,t)) args'
    body' <- withVars argctx $ traverse lowerExpr body
    b' <- bindCDepBind args' (retTy', body')
    return $ CDef name b'

lowerUserFunc :: CUserFunc FormatTy -> EM (CUserFunc VerusTy)
lowerUserFunc (CUserFunc name b) = do
    (args, (retTy, body)) <- unbindCDepBind b
    args' <- mapM lowerArg args
    retTy' <- lowerTy retTy
    body' <- traverseCAExpr lowerTy body
    b' <- bindCDepBind args' (retTy', body')
    return $ CUserFunc name b'


lowerFieldTy :: FormatTy -> EM VerusTy
-- lowerFieldTy (FHexConst s) = return RTUnit
lowerFieldTy = lowerTy -- for now, probably need to change it later


maybeLenOf :: FormatTy -> EM (Maybe ConstUsize)
maybeLenOf (FBuf (Just flen)) = return $ Just $ lowerFLen flen
maybeLenOf (FHexConst s) = return $ Just $ CUsizeLit $ length s `div` 2
maybeLenOf _ = return Nothing

lowerTyDef :: String -> CTyDef FormatTy -> EM (Maybe (CTyDef (Maybe ConstUsize, VerusTy)))
lowerTyDef _ (CStructDef (CStruct name fields isVest)) = do
    let lowerField (n, t) = do
            t' <- lowerFieldTy t
            l <- maybeLenOf t
            return (n, (l, t'))
    fields' <- mapM lowerField fields
    return $ Just $ CStructDef $ CStruct name fields' isVest
lowerTyDef _ (CEnumDef (CEnum name cases isVest)) = do
    let lowerCase (n, t) = do
            tt' <- case t of
                Just t -> do
                    t' <- lowerFieldTy t
                    l <- maybeLenOf t
                    return $ Just (l, t')
                Nothing -> return Nothing
            return (n, tt')
    cases' <- mapM lowerCase $ M.assocs cases
    return $ Just $ CEnumDef $ CEnum name (M.fromList cases') isVest

lowerName :: (String, FLen, Int) -> EM (String, ConstUsize, Int)
lowerName (n, l, i) = do
    let l' = lowerFLen l
    return (n, l', i)



--------------------------------------------------------------------------------
-- Helper functions

vecU8 :: VerusTy
vecU8 = RTVec RTU8

arrayU8 :: ConstUsize -> VerusTy
arrayU8 n = RTArray RTU8 n
