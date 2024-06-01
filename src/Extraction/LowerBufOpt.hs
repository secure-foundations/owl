{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
import Control.Monad.State
import Control.Monad.Except
import Control.Lens
import Prettyprinter
import Pretty
import Data.Type.Equality
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Name
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

newtype LowerMonad t a = LowerMonad (StateT LowerEnv (ExtractionMonad t) a)
    deriving (Functor, Applicative, Monad, MonadState LowerEnv, MonadIO, MonadError ExtractionError)

data LowerEnv = LowerEnv {
    _lowerCtx :: M.Map (CDataVar FormatTy) LowerTCVal
}


type CLetBinding = (CDataVar VerusTy, Maybe AST.AExpr, CExpr VerusTy)

data Suspendable a = 
    Eager a
    | Susp (Suspended a)

type CWithLets a = (a, [CLetBinding])
type CAWithLets = CWithLets (CAExpr VerusTy)
type CEWithLets = CWithLets (CExpr VerusTy)

data Suspended a = Suspended {
    scTy :: VerusTy,
    scComputation :: VerusTy -> LM (a, VerusTy)
} 


instance Fresh (LowerMonad t) where
    fresh (Fn s _) = do
        n <- liftEM $ use freshCtr
        liftEM $ freshCtr %= (+) 1
        return $ Fn s n
    fresh nm@(Bn {}) = return nm

initLEnv :: LowerEnv
initLEnv = LowerEnv M.empty

runLowerMonad :: LowerMonad t a -> ExtractionMonad t a
runLowerMonad (LowerMonad m) = evalStateT m initLEnv

liftEM :: ExtractionMonad t a -> LowerMonad t a
liftEM = LowerMonad . lift

-- The type context stores either the type of eagerly evaluated variables,
-- or a list of letbindings to be inserted before the current call site to
-- force a suspended computation.
data LowerTCVal = 
    LTCTy VerusTy
    | LTCSusp (Suspended [CLetBinding])

type LM = LowerMonad FormatTy


makeLenses ''LowerEnv


lowerTy' :: FormatTy -> LM VerusTy
lowerTy' = liftEM . lowerTy

withVars :: [(CDataVar FormatTy, VerusTy)] -> LM a -> LM a
withVars xs k = do
    s <- use lowerCtx
    let tcmap = M.fromList $ map (\(x,t) -> (x, LTCTy t)) xs
    lowerCtx %= mappend tcmap
    res <- k
    lowerCtx .= s
    return res

withSusp :: [(CDataVar FormatTy, Suspended [CLetBinding])] -> LM a -> LM a
withSusp xs k = do
    s <- use lowerCtx
    let tcmap = M.fromList $ map (\(x,t) -> (x, LTCSusp t)) xs
    lowerCtx %= mappend tcmap
    res <- k
    lowerCtx .= s
    return res

lookupLTC :: CDataVar FormatTy -> LM LowerTCVal
lookupLTC v = do
    ctx <- use lowerCtx
    case M.lookup v ctx of
        Just x -> return x
        Nothing -> throwError $ UndefinedSymbol $ "LowerBufOpt.tyOf: " ++ show v

forceAE :: Suspendable CAWithLets -> LM (CAExpr VerusTy, [CLetBinding])
forceAE (Eager x) = return x
forceAE (Susp sc) = do
    let t = scTy sc
    ((x, lets), t') <- scComputation sc t
    return (x, lets)

forceAEs :: [Suspendable CAWithLets] -> LM ([CAExpr VerusTy], [CLetBinding])
forceAEs xs = do
    xs' <- mapM forceAE xs
    let (ys, zss) = unzip xs'
    return (ys, concat zss)

exprFromLets :: [CLetBinding] -> CExpr VerusTy -> CExpr VerusTy
exprFromLets lets e = foldr (\(x, oanf, e') acc -> Typed (acc ^. tty) $ CLet e' oanf $ bind x acc) e lets

forceE :: Suspendable CEWithLets -> LM (CExpr VerusTy)
forceE (Eager (x, lets)) = return $ exprFromLets lets x
forceE (Susp sc) = do
    let t = scTy sc
    ((x, lets), t') <- scComputation sc t
    return $ exprFromLets lets x


getSuspTy :: Suspendable CAWithLets -> VerusTy
getSuspTy (Eager (Typed t _, _)) = t
getSuspTy (Susp s) = scTy s

mkApp :: String -> FormatTy -> [Suspendable CAWithLets] -> LM (Suspendable CAWithLets)
mkApp f frty args' = do
    case (f, frty) of
        ("enc_st_aead", _) -> do 
            (argrtys, arglets) <- forceAEs args'
            let frty' = RTStAeadBuilder
            let suspcomp rt = do
                        liftEM $ debugPrint $ "enc_st_aead_builder used at type: " ++ show rt
                        let ae = Typed frty' $ CAApp "enc_st_aead_builder" argrtys
                        return ((ae, arglets), frty')
            return $ Susp $ Suspended frty' suspcomp
        (f, FStruct f' fields) | f == f' -> do
            let argtys = map getSuspTy args'
            if RTStAeadBuilder `elem` argtys then do
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
                frty' <- lowerTy' frty
                let suspcomp rt = do
                        serializedTy <- lowerTy' $ FBuf Nothing
                        case rt of
                            rt' | rt' == frty' -> do
                                -- We want the struct as an actual Rust struct, so return it as normal
                                (argrtys, arglets) <- forceAEs args'
                                return ((Typed frty' $ CAApp f argrtys, arglets), frty')
                            rt' | rt' == serializedTy -> do
                                let parsleycombof (fieldFormatTy, argVerusTy) =
                                        if argVerusTy == RTStAeadBuilder then return PCBuilder else liftEM $ execParsleyCombOf f' fieldFormatTy
                                combs <- mapM parsleycombof $ zip (map snd fields) argtys
                                (argrtys, arglets) <- forceAEs args'
                                return ((Typed serializedTy $ CASerializeWith frty' (zip argrtys combs), arglets), frty')
                            _ -> throwError $ ErrSomethingFailed "mkApp struct constructor: got bad type"
                return $ Susp $ Suspended frty' suspcomp
            else do
                (argrtys, arglets) <- forceAEs args'
                frty' <- lowerTy' frty
                return $ addLets (Eager (Typed frty' $ CAApp f argrtys , [])) arglets
        _ -> do
            (argrtys, arglets) <- forceAEs args'
            frty' <- lowerTy' frty
            return $ addLets (Eager (Typed frty' $ CAApp f argrtys , [])) arglets

addLets :: Suspendable (CWithLets a) -> [CLetBinding] -> Suspendable (CWithLets a)
addLets (Eager (x, lets)) lets' = Eager (x, lets ++ lets')
addLets (Susp sc) lets' = Susp $ sc { scComputation = \rt -> do
    ((x, lets), t) <- scComputation sc rt
    return ((x, lets ++ lets'), t)
}

data LowerCAExprInfo = LowerCAExprInfo {
    inArg :: Bool
} deriving (Show, Eq)

lowerCAExpr :: LowerCAExprInfo -> CAExpr FormatTy -> LM (Suspendable CAWithLets)
lowerCAExpr info aexpr = do
    rt <- lowerTy' $ aexpr ^. tty
    let eager x = return $ Eager (x, [])
    let eagerRt x = eager $ Typed rt x :: LM (Suspendable CAWithLets)
    let lowerGet ae = if inArg info then eager $ Typed u8slice ae else eagerRt ae
    case aexpr ^. tval of
        CAVar s n -> do
            ltcv <- lookupLTC n 
            case ltcv of
                LTCTy t -> eagerRt $ CAVar s (castName n)
                LTCSusp sc -> do
                    let suspcomp rt = do
                            (lets, rt') <- scComputation sc rt
                            return ((Typed rt $ CAVar s (castName n), lets), rt')
                    return $ Susp $ Suspended (scTy sc) suspcomp
        CAApp f args -> do
            args' <- mapM (lowerCAExpr info { inArg = True }) args
            mkApp f (aexpr ^. tty) args'
        CAGet s -> lowerGet $ CAGet s
        CAGetEncPK s -> lowerGet $ CAGetEncPK s
        CAGetVK s -> lowerGet $ CAGetVK s
        CAInt fl -> eagerRt $ CAInt fl
        CAHexConst s -> do
            hcvar <- fresh $ s2n "hexconst"
            let lets = [(hcvar, Nothing, Typed rt $ CRet $ Typed rt $ CAHexConst s)]
            return $ Eager (Typed rt $ CAVar (ignore "hexconst") hcvar, lets)
        CACounter s -> eagerRt $ CACounter s
        CASerializeWith t args -> do
            throwError $ ErrSomethingFailed "got CASerializeWith as input to lowering, it should not be emitted by Concretify"


lowerExprNoSusp :: CExpr FormatTy -> LM (CExpr VerusTy)
lowerExprNoSusp expr = do
    expr' <- lowerExpr expr
    case expr' of
        Eager (x, lets) -> return $ exprFromLets lets x
        Susp _ -> throwError $ ErrSomethingFailed "got suspended computation in lowerExprNoSusp"

lowerExpr :: CExpr FormatTy -> LM (Suspendable CEWithLets)
lowerExpr expr = do
    rt <- lowerTy' $ expr ^. tty
    let lowerCAExpr' = lowerCAExpr (LowerCAExprInfo { inArg = False })
    let eager x = return $ Eager x
    let eagerNoLets x = eager $ (x, []) :: LM (Suspendable CEWithLets)
    let eagerRt x lets = eager $ (Typed rt x, lets) :: LM (Suspendable CEWithLets)
    let eagerRtNoLets x = eagerNoLets $ Typed rt x :: LM (Suspendable CEWithLets)
    case expr ^. tval of
        CSkip -> eagerRtNoLets CSkip
        CRet ae -> do
            ae' <- lowerCAExpr' ae
            case ae' of
                Eager (ae', aelets) -> eager (Typed (ae' ^. tty) $ CRet ae', aelets)
                Susp s -> do
                    let suspcomp rt = do
                            ((ae'', aelets), rt') <- scComputation s $ rt
                            return ((Typed (ae'' ^. tty) $ CRet ae'', aelets), rt')
                    return $ Susp $ Suspended (scTy s) suspcomp
        CInput ft xek -> do
            ((x, ev), k) <- unbind xek
            frt <- lowerTy' ft
            k' <- withVars [(x, frt)] $ lowerExprNoSusp k
            let xek' = bind (castName x, ev) k'
            eagerNoLets $ Typed (k' ^. tty) $ CInput frt xek'
        COutput ae dst -> do
            ae' <- lowerCAExpr' ae
            case ae' of
                Eager (ae', aeLets) -> eagerRt (COutput ae' dst) aeLets
                Susp sc -> do
                    -- Force the computation at type Buffer
                    outputTy <- lowerTy' $ FBuf Nothing
                    ((ae'', aeLets), _) <- scComputation sc $ outputTy
                    eagerRt (COutput ae'' dst) aeLets
        CSample flen t xk -> do
            (x, k) <- unbind xk
            t' <- lowerTy' t
            k' <- withVars [(x, t')] $ lowerExprNoSusp k
            let xk' = bind (castName x) k'
            eagerNoLets $ Typed (k' ^. tty) $ CSample flen t' xk'
        CLet e oanf xk -> do
            (x, k) <- unbind xk
            e' <- lowerExpr e
            case e' of
                Eager (e'', elets) -> do
                    k' <- withVars [(x, e'' ^. tty)] $ lowerExprNoSusp k
                    let xk' = bind (castName x) k'
                    eagerNoLets $ exprFromLets elets $ Typed (k' ^. tty) $ CLet e'' oanf xk'
                Susp (Suspended scTy sccomp) -> do
                    let sccompLet t = do
                            ((e'', elets), t') <- sccomp t
                            let lets = elets ++ [(castName x, oanf, e'')]
                            -- When this computation is later forced, we update the context to reflect this
                            -- TODO: make sure that this doesn't result in duplication
                            lowerCtx %= M.insert x (LTCTy t)
                            return (lets, t')
                    k' <- withSusp [ (castName x, Suspended scTy sccompLet) ] $ lowerExprNoSusp k
                    eagerNoLets k'                    
        CBlock e -> do
            e' <- lowerExpr e >>= forceE
            eagerNoLets $ Typed (e' ^. tty) $ CBlock e'
        CIf ae e1 e2 -> do
            (ae', aelets) <- lowerCAExpr' ae >>= forceAE
            e1' <- lowerExpr e1 >>= forceE
            e2' <- lowerExpr e2 >>= forceE
            eagerNoLets $ exprFromLets aelets $ Typed rt $ CIf ae' e1' e2'
        CCase ae cases -> do
            (ae', aelets) <- lowerCAExpr' ae >>= forceAE
            cases' <- forM cases $ \(n, c) -> do
                case c of
                    Left k -> do
                        k' <- lowerExprNoSusp k
                        return (n, Left k')
                    Right xtk -> do
                        (x, (t, k)) <- unbind xtk
                        t' <- lowerTy' t
                        k' <- withVars [(x, t')] $ lowerExprNoSusp k
                        return (n, Right $ bind (castName x) (t', k'))
            eagerNoLets $ exprFromLets aelets $ Typed rt $ CCase ae' cases'
        CCall fn frty args -> do
            frty' <- lowerTy' frty
            args' <- mapM lowerCAExpr' args
            (args'', arglets) <- forceAEs args'
            eagerNoLets $ exprFromLets arglets $ Typed frty' $ CCall fn frty' args''
        CParse pk ae dst_ty otw xtsk -> do
            (xts, k) <- unbind xtsk
            xts' <- mapM (\(n, s, t) -> do t' <- lowerTy' t ; return (castName n, s, t')) xts
            let ctx = map (\(x, _, t) -> (castName x, t)) xts'
            (ae', aeLets) <- lowerCAExpr' ae >>= forceAE
            dst_ty' <- lowerTy' dst_ty
            otw' <- traverse (lowerExpr >=> forceE) otw
            k' <- withVars ctx $ lowerExprNoSusp k
            let xtsk' = bind xts' k'
            eagerNoLets $ exprFromLets aeLets $ Typed (k' ^. tty) $ CParse pk ae' dst_ty' otw' xtsk'
        CTLookup s ae -> do
            (ae', aelets) <- lowerCAExpr' ae >>= forceAE
            eagerNoLets $ exprFromLets aelets $ Typed rt $ CTLookup s ae'
        CTWrite s ae1 ae2 -> do
            (ae1', ae1lets) <- lowerCAExpr' ae1 >>= forceAE
            (ae2', ae2lets) <- lowerCAExpr' ae2 >>= forceAE
            eagerNoLets $ exprFromLets (ae1lets ++ ae2lets) $ Typed rt $ CTWrite s ae1' ae2'
        CGetCtr s -> do
            eagerRtNoLets $ CGetCtr s
        CIncCtr s -> do
            eagerRtNoLets $ CIncCtr s
        

lowerArg :: (CDataVar FormatTy, String, FormatTy) -> LM (CDataVar VerusTy, String, VerusTy)
lowerArg (n, s, t) = do
    t' <- lowerTy' t
    return (castName n, s, t')



lowerDef' :: CDef FormatTy -> LM (CDef VerusTy)
lowerDef' (CDef name b) = do
    (args, (retTy, body)) <- liftEM $ unbindCDepBind b
    args' <- mapM lowerArg args
    retTy' <- lowerTy' retTy
    let argctx = map (\(v,_,t) -> (castName v,t)) args'
    body' <- withVars argctx $ traverse lowerExprNoSusp body
    b' <- liftEM $ bindCDepBind args' (retTy', body')
    return $ CDef name b'

lowerUserFunc' :: CUserFunc FormatTy -> LM (CUserFunc VerusTy)
lowerUserFunc' (CUserFunc name b) = do
    (args, (retTy, body)) <- liftEM $ unbindCDepBind b
    args' <- mapM lowerArg args
    retTy' <- lowerTy' retTy
    body' <- traverseCAExpr lowerTy' body
    b' <- liftEM $ bindCDepBind args' (retTy', body')
    return $ CUserFunc name b'

lowerDef :: CDef FormatTy -> EM (CDef VerusTy)
lowerDef = runLowerMonad . lowerDef'

lowerUserFunc :: CUserFunc FormatTy -> EM (CUserFunc VerusTy)
lowerUserFunc = runLowerMonad . lowerUserFunc'

-------------------------------------------------------------------------------------------
--- Structs and enums

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

u8slice :: VerusTy
u8slice = RTRef RShared (RTSlice RTU8)
