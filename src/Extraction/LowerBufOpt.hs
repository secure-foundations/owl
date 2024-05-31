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
import qualified AST
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

data Suspended = SuspendedComputation {
    scTy :: VerusTy,
    -- Map from desired return type to the aexpr for the current call site, 
    -- plus any letbindings that need to be inserted before the current call site
    scComputation :: VerusTy -> EM (CAExpr VerusTy, [CLetBinding])
} 

type CLetBinding = (CDataVar VerusTy, Maybe AST.AExpr, CExpr VerusTy)


data Suspendable a = 
    Eager (a, [CLetBinding]) -- any letbindings that need to be evaluated before the current computation
    | Susp Suspended


forceAE :: Suspendable (CAExpr VerusTy) -> EM (CAExpr VerusTy, [CLetBinding])
forceAE (Eager x) = return x
forceAE (Susp _) = throwError $ ErrSomethingFailed "TODO force suspended computation"

forceAEs :: [Suspendable (CAExpr VerusTy)] -> EM ([CAExpr VerusTy], [CLetBinding])
forceAEs xs = do
    xs' <- mapM forceAE xs
    let (ys, zss) = unzip xs'
    return (ys, concat zss)

mkApp :: String -> FormatTy -> [CAExpr VerusTy] -> EM (Suspendable (CAExpr VerusTy))
mkApp f frty argrtys = do
    let eager x = return $ Eager (x, [])
    case (f, frty) of
        ("enc_st_aead", _) -> do 
            let frty = RTStAeadBuilder
            eager $ Typed frty $ CAApp "enc_st_aead_builder" argrtys
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
                eager $ Typed frty' $ CAApp f argrtys 
            else do
                frty' <- lowerTy frty
                eager $ Typed frty' $ CAApp f argrtys 
        _ -> do
            frty' <- lowerTy frty
            eager $ Typed frty' $ CAApp f argrtys

addLets :: Suspendable a -> [CLetBinding] -> Suspendable a
addLets (Eager (x, lets)) lets' = Eager (x, lets ++ lets')
addLets (Susp sc) lets' = Susp $ sc { scComputation = \rt -> do
    (x, lets) <- scComputation sc rt
    return (x, lets ++ lets')
}

lowerCAExpr :: CAExpr FormatTy -> EM (Suspendable (CAExpr VerusTy))
lowerCAExpr aexpr = do
    rt <- lowerTy $ aexpr ^. tty
    let eager x = return $ Eager (x, [])
    let eagerRt x = eager $ Typed rt x :: EM (Suspendable (CAExpr VerusTy))
    case aexpr ^. tval of
        CAVar s n -> do
            rtFromCtx <- tyOf n
            eager $ Typed rtFromCtx $ CAVar s (castName n)
        CAApp f args -> do
            args' <- mapM lowerCAExpr args
            (args'', arglets) <- forceAEs args'
            app <- mkApp f (aexpr ^. tty) args''
            return $ addLets app arglets
        CAGet s -> eagerRt $ CAGet s
        CAGetEncPK s -> eagerRt $ CAGetEncPK s
        CAGetVK s -> eagerRt $ CAGetVK s
        CAInt fl -> eagerRt $ CAInt fl
        CAHexConst s -> eagerRt $ CAHexConst s
        CACounter s -> eagerRt $ CACounter s


exprFromLets :: [CLetBinding] -> CExpr VerusTy -> CExpr VerusTy
exprFromLets lets e = foldr (\(x, oanf, e') acc -> Typed (acc ^. tty) $ CLet e' oanf $ bind x acc) e lets

forceE :: Suspendable (CExpr VerusTy) -> EM (CExpr VerusTy)
forceE (Eager (x, lets)) = return $ exprFromLets lets x
forceE (Susp _) = throwError $ ErrSomethingFailed "TODO force suspended computation"




lowerExprNoSusp :: CExpr FormatTy -> EM (CExpr VerusTy)
lowerExprNoSusp expr = do
    expr' <- lowerExpr expr
    case expr' of
        Eager (x, lets) -> return $ exprFromLets lets x
        Susp _ -> throwError $ ErrSomethingFailed "got suspended computation in lowerExprNoSusp"

lowerExpr :: CExpr FormatTy -> EM (Suspendable (CExpr VerusTy))
lowerExpr expr = do
    rt <- lowerTy $ expr ^. tty
    let eager x = return $ Eager x
    let eagerNoLets x = eager $ (x, []) :: EM (Suspendable (CExpr VerusTy))
    let eagerRt x lets = eager $ (Typed rt x, lets) :: EM (Suspendable (CExpr VerusTy))
    let eagerRtNoLets x = eagerNoLets $ Typed rt x :: EM (Suspendable (CExpr VerusTy))
    case expr ^. tval of
        CSkip -> eagerRtNoLets CSkip
        CRet ae -> do
            ae' <- lowerCAExpr ae
            case ae' of
                Eager (ae', aelets) -> eager (Typed (ae' ^. tty) $ CRet ae', aelets)
                Susp ae' -> throwError $ ErrSomethingFailed "TODO susp"
        CInput ft xek -> do
            ((x, ev), k) <- unbind xek
            frt <- lowerTy ft
            k' <- withVars [(x, frt)] $ lowerExprNoSusp k
            let xek' = bind (castName x, ev) k'
            eagerNoLets $ Typed (k' ^. tty) $ CInput frt xek'
        COutput ae dst -> do
            ae' <- lowerCAExpr ae
            case ae' of
                Eager (ae', aeLets) -> eagerRt (COutput ae' dst) aeLets
                Susp ae' -> throwError $ ErrSomethingFailed "TODO susp for output"
        CSample flen t xk -> do
            (x, k) <- unbind xk
            t' <- lowerTy t
            k' <- withVars [(x, t')] $ lowerExprNoSusp k
            let xk' = bind (castName x) k'
            eagerNoLets $ Typed (k' ^. tty) $ CSample flen t' xk'
        CLet e oanf xk -> do
            (x, k) <- unbind xk
            e' <- lowerExpr e
            (e'', elets) <- case e' of
                Eager e' -> return e'
                Susp e' -> throwError $ ErrSomethingFailed "TODO susp for let"
            k' <- withVars [(x, e'' ^. tty)] $ lowerExprNoSusp k
            let xk' = bind (castName x) k'
            eagerNoLets $ exprFromLets elets $ Typed (k' ^. tty) $ CLet e'' oanf xk'
        CBlock e -> do
            e' <- lowerExpr e >>= forceE
            eagerNoLets $ Typed (e' ^. tty) $ CBlock e'
        CIf ae e1 e2 -> do
            (ae', aelets) <- lowerCAExpr ae >>= forceAE
            e1' <- lowerExpr e1 >>= forceE
            e2' <- lowerExpr e2 >>= forceE
            eagerNoLets $ exprFromLets aelets $ Typed rt $ CIf ae' e1' e2'
        CCase ae cases -> do
            (ae', aelets) <- lowerCAExpr ae >>= forceAE
            cases' <- forM cases $ \(n, c) -> do
                case c of
                    Left k -> do
                        k' <- lowerExprNoSusp k
                        return (n, Left k')
                    Right xtk -> do
                        (x, (t, k)) <- unbind xtk
                        t' <- lowerTy t
                        k' <- withVars [(x, t')] $ lowerExprNoSusp k
                        return (n, Right $ bind (castName x) (t', k'))
            eagerNoLets $ exprFromLets aelets $ Typed rt $ CCase ae' cases'
        CCall fn frty args -> do
            frty' <- lowerTy frty
            args' <- mapM lowerCAExpr args
            (args'', arglets) <- forceAEs args'
            eagerNoLets $ exprFromLets arglets $ Typed frty' $ CCall fn frty' args''
        CParse pk ae dst_ty otw xtsk -> do
            (xts, k) <- unbind xtsk
            xts' <- mapM (\(n, s, t) -> do t' <- lowerTy t ; return (castName n, s, t')) xts
            let ctx = map (\(x, _, t) -> (castName x, t)) xts'
            (ae', aeLets) <- lowerCAExpr ae >>= forceAE
            dst_ty' <- lowerTy dst_ty
            otw' <- traverse (lowerExpr >=> forceE) otw
            k' <- withVars ctx $ lowerExprNoSusp k
            let xtsk' = bind xts' k'
            eagerNoLets $ exprFromLets aeLets $ Typed (k' ^. tty) $ CParse pk ae' dst_ty' otw' xtsk'
        CTLookup s ae -> do
            (ae', aelets) <- lowerCAExpr ae >>= forceAE
            eagerNoLets $ exprFromLets aelets $ Typed rt $ CTLookup s ae'
        CTWrite s ae1 ae2 -> do
            (ae1', ae1lets) <- lowerCAExpr ae1 >>= forceAE
            (ae2', ae2lets) <- lowerCAExpr ae2 >>= forceAE
            eagerNoLets $ exprFromLets (ae1lets ++ ae2lets) $ Typed rt $ CTWrite s ae1' ae2'
        CGetCtr s -> do
            eagerRtNoLets $ CGetCtr s
        CIncCtr s -> do
            eagerRtNoLets $ CIncCtr s
        

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
    body' <- withVars argctx $ traverse lowerExprNoSusp body
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
