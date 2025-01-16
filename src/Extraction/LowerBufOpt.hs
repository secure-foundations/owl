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
lowerTy (FBuf BufPublic Nothing) = return $ RTOwlBuf AnyLifetime
lowerTy (FBuf BufPublic (Just flen)) = return $ RTOwlBuf AnyLifetime
lowerTy (FBuf BufSecret Nothing) = return $ RTSecBuf AnyLifetime
lowerTy (FBuf BufSecret (Just flen)) = return $ RTSecBuf AnyLifetime
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
lowerTy FDeclassifyTok = return RTDeclassifyTok

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
    -- The choices for the type of the suspended computation
    scTyChoices :: [VerusTy],
    -- The computation to perform when the computation is forced
    -- (only works when given one of the choices in scTyChoices)
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

forceAE :: VerusTy -> Suspendable CAWithLets -> LM (CAExpr VerusTy, [CLetBinding])
forceAE _ (Eager x) = return x
forceAE t (Susp sc) = do
    ((x, lets), t') <- scComputation sc t
    return (x, lets)

forceAEs :: [VerusTy] -> [Suspendable CAWithLets] -> LM ([CAExpr VerusTy], [CLetBinding])
forceAEs tys xs = do
    xs' <- zipWithM forceAE tys xs
    let (ys, zss) = unzip xs'
    return (ys, concat zss)

exprFromLets :: [CLetBinding] -> CExpr VerusTy -> CExpr VerusTy
exprFromLets lets e = foldr (\(x, oanf, e') acc -> Typed (acc ^. tty) $ CLet e' oanf $ bind x acc) e lets

forceE :: VerusTy -> Suspendable CEWithLets -> LM (CExpr VerusTy)
forceE _ (Eager (x, lets)) = return $ exprFromLets lets x
forceE t (Susp sc) = do
    ((x, lets), t') <- scComputation sc t
    return $ exprFromLets lets x


getSuspTy :: Suspendable CAWithLets -> [VerusTy]
getSuspTy (Eager (Typed t _, _)) = [t]
getSuspTy (Susp s) = scTyChoices s

mkApp :: String -> String -> FormatTy -> [VerusTy] -> [Suspendable CAWithLets] -> LM (Suspendable CAWithLets)
mkApp f spec_f frty argtys args' = do
    case (f, frty) of
        ("enc_st_aead", _) -> do 
            (argrtys, arglets) <- forceAEs argtys args'
            serializedTy <- getSerializedTy
            let frtyChoices = [RTStAeadBuilder, serializedTy]
            let suspcomp rt = do
                    case rt of
                        RTStAeadBuilder -> do
                            let ae = Typed RTStAeadBuilder $ CAApp "enc_st_aead_builder" spec_f argrtys
                            return ((ae, arglets), RTStAeadBuilder)
                        tt' | tt' == serializedTy -> do
                            let ae = Typed serializedTy $ CAApp "enc_st_aead" spec_f argrtys
                            return ((ae, arglets), serializedTy)
                        _ -> throwError $ ErrSomethingFailed "mkApp enc_st_aead_builder: got bad type"
            return $ Susp $ Suspended frtyChoices suspcomp
        (f, FStruct f' fields) | f == f' -> do
            let argsusptys = map getSuspTy args'
            if RTStAeadBuilder `elem` concat argsusptys then do
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


                let mkBuilderStructField (fieldName, fieldFormatTy) argVerusTyChoices = do
                        if RTStAeadBuilder `elem` argVerusTyChoices 
                        then return (execName fieldName, RTStAeadBuilder) 
                        else (,) (execName fieldName) <$> lowerTy' fieldFormatTy
                builderStructFields <- zipWithM mkBuilderStructField fields argsusptys
                let rStructTy' = RTStruct (execName f') builderStructFields
                -- serStructTy <- lowerTy' frty
                serializedTy <- getSerializedTy
                let suspcomp rt = do
                        case rt of
                            -- Owl enforces that there cannot be two different struct declarations with the same name,
                            -- so we only need to check that the struct names are equal
                            RTStruct rn' rfs' | rn' == execName f' -> do
                                -- We want the struct as an actual Rust struct, so return it as normal
                                (argrtys, arglets) <- forceAEs argtys args'
                                return ((Typed rStructTy' $ CAApp f spec_f argrtys, arglets), rStructTy')
                            rt' | rt' == serializedTy -> do
                                -- We want the struct as a serialized buffer, so we serialize it using the builder combinator
                                let parsleycombof (fieldFormatTy, argVerusTyChoices) =
                                        if RTStAeadBuilder `elem` argVerusTyChoices then return PCBuilder else liftEM $ execParsleyCombOf f' fieldFormatTy
                                let forceTyOf fieldVerusTy argVerusTyChoices = 
                                        if RTStAeadBuilder `elem` argVerusTyChoices then RTStAeadBuilder else fieldVerusTy
                                combs <- mapM parsleycombof $ zip (map snd fields) argsusptys
                                let forcetys = zipWith forceTyOf argtys argsusptys
                                (argrtys, arglets) <- forceAEs forcetys args' 
                                -- CASerializeWith needs serStructTy since that is the type that will determine
                                return ((Typed serializedTy $ CASerializeWith rStructTy' (zip argrtys combs), arglets), rStructTy')
                            _ -> throwError $ ErrSomethingFailed "mkApp struct constructor: got bad type"
                return $ Susp $ Suspended [rStructTy', serializedTy] suspcomp
            else do
                (argrtys, arglets) <- forceAEs argtys args'
                frty' <- lowerTy' frty
                return $ addLets (Eager (Typed frty' $ CAApp f spec_f argrtys , [])) arglets
        _ -> do
            (argrtys, arglets) <- forceAEs argtys args'
            frty' <- lowerTy' frty
            return $ addLets (Eager (Typed frty' $ CAApp f spec_f argrtys , [])) arglets

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
    let lowerGet ae = eagerRt ae -- if inArg info then eager $ Typed u8slice ae else eagerRt ae
    case aexpr ^. tval of
        CAVar s n -> do
            ltcv <- lookupLTC n 
            case ltcv of
                LTCTy t -> eager $ Typed t $ CAVar s (castName n)
                LTCSusp sc -> do
                    let suspcomp rt = do
                            (lets, rt') <- scComputation sc rt
                            return ((Typed rt $ CAVar s (castName n), lets), rt')
                    return $ Susp $ Suspended (scTyChoices sc) suspcomp
        CAApp f spec_f args -> do
            argtys <- mapM (lowerTy' . (^. tty)) args
            args' <- mapM (lowerCAExpr info { inArg = True }) args
            mkApp f spec_f (aexpr ^. tty) argtys args'
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
        CACast ae t -> do
            ae' <- lowerCAExpr info ae
            t' <- lowerTy' t
            case ae' of
                Eager (ae', aelets) -> eagerRt $ CACast ae' t'
                Susp s -> do
                    let suspcomp rt = do
                            ((ae'', aelets), rt') <- scComputation s $ rt
                            return ((Typed rt $ CACast ae'' t', aelets), rt')
                    return $ Susp $ Suspended (scTyChoices s) suspcomp

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
                    return $ Susp $ Suspended (scTyChoices s) suspcomp
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
                    outputTy <- getSerializedTy
                    ((ae'', aeLets), resTy) <- scComputation sc $ outputTy
                    case (resTy, ae ^. tval) of
                        (RTStruct _ fs, CAVar _ x) | RTStAeadBuilder `elem` map snd fs -> do
                            -- Special case for fused serialize-output
                            let x' = castName x
                            aeForX <- case find (\(xlet, _, _) -> xlet == x') aeLets of
                                Just (_, _, rhs) -> do
                                    case rhs ^. tval of
                                        CRet ae -> return ae
                                        _ -> throwError $ ErrSomethingFailed "COutput fused serialize opt: could not find rhs for x"
                                Nothing -> throwError $ ErrSomethingFailed "COutput fused serialize opt: could not find rhs for x"
                            let aeLetsNoX = filter (\(xlet, _, _) -> xlet /= x') aeLets
                            eagerRt (COutput aeForX dst) aeLetsNoX
                        _ -> eagerRt (COutput ae'' dst) aeLets
        CSample flen t xk -> do
            (x, k) <- unbind xk
            t' <- lowerTy' t
            k' <- withVars [(x, t')] $ lowerExprNoSusp k
            let xk' = bind (castName x) k'
            eagerNoLets $ Typed (k' ^. tty) $ CSample flen t' xk'
        CItreeDeclassify dop xk -> do 
            (x, k) <- unbind xk
            k' <- withVars [(x, RTDeclassifyTok)] $ lowerExprNoSusp k
            dop' <- traverseDeclassifyingOp lowerTy' dop
            let xk' = bind (castName x) k'
            eagerNoLets $ Typed (k' ^. tty) $ CItreeDeclassify dop' xk'
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
                            -- liftEM $ debugPrint $ "Adding let bindings for: " ++ show x ++ " at type: " ++ show t'
                            lowerCtx %= M.insert x (LTCTy t')
                            return (lets, t')
                    k' <- withSusp [ (castName x, Suspended scTy sccompLet) ] $ lowerExprNoSusp k
                    eagerNoLets k'                    
        CBlock e -> do
            eTy <- lowerTy' $ e ^. tty
            e' <- lowerExpr e >>= forceE eTy
            eagerNoLets $ Typed (e' ^. tty) $ CBlock e'
        CIf ae e1 e2 -> do
            aety <- lowerTy' $ ae ^. tty
            e1ty <- lowerTy' $ e1 ^. tty
            e2ty <- lowerTy' $ e2 ^. tty
            (ae', aelets) <- lowerCAExpr' ae >>= forceAE aety
            e1' <- lowerExpr e1 >>= forceE e1ty
            e2' <- lowerExpr e2 >>= forceE e2ty
            eagerNoLets $ exprFromLets aelets $ Typed rt $ CIf ae' e1' e2'
        CCase ae cases -> do
            aety <- lowerTy' $ ae ^. tty
            (ae', aelets) <- lowerCAExpr' ae >>= forceAE aety
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
            argtys <- mapM (lowerTy' . (^. tty)) args
            args' <- mapM lowerCAExpr' args
            (args'', arglets) <- forceAEs argtys args'
            eagerNoLets $ exprFromLets arglets $ Typed frty' $ CCall fn frty' args''
        CParse pk ae extraArgs dst_ty otw xtsk -> do
            (xts, k) <- unbind xtsk
            xts' <- mapM (\(n, s, t) -> do t' <- lowerTy' t ; return (castName n, s, t')) xts
            let ctx = map (\(x, _, t) -> (castName x, t)) xts'
            aety <- lowerTy' $ ae ^. tty
            (ae', aeLets) <- lowerCAExpr' ae >>= forceAE aety
            extraArgsSusp <- mapM lowerCAExpr' extraArgs
            extraArgsTys <- mapM (lowerTy' . (^. tty)) extraArgs
            (extraArgs', extraArgsLets) <- forceAEs extraArgsTys extraArgsSusp
            dst_ty' <- lowerTy' dst_ty
            otw' <- case otw of
                Nothing -> return Nothing
                Just otw -> do
                    otwty <- (lowerTy' . (^. tty)) otw
                    Just <$> (lowerExpr >=> forceE otwty) otw
            k' <- withVars ctx $ lowerExprNoSusp k
            let xtsk' = bind xts' k'
            eagerNoLets $ exprFromLets (aeLets ++ extraArgsLets) $ Typed (k' ^. tty) $ CParse pk ae' extraArgs' dst_ty' otw' xtsk'
        CTLookup s ae -> do
            aety <- lowerTy' $ ae ^. tty
            (ae', aelets) <- lowerCAExpr' ae >>= forceAE aety
            eagerNoLets $ exprFromLets aelets $ Typed rt $ CTLookup s ae'
        CTWrite s ae1 ae2 -> do
            ae1ty <- lowerTy' $ ae1 ^. tty
            ae2ty <- lowerTy' $ ae2 ^. tty
            (ae1', ae1lets) <- lowerCAExpr' ae1 >>= forceAE ae1ty
            (ae2', ae2lets) <- lowerCAExpr' ae2 >>= forceAE ae2ty
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
    liftEM $ debugLog $ "Buffer optimizing lowering def: " ++ name
    (args, (retTy, body)) <- liftEM $ unbindCDepBind b
    args' <- mapM lowerArg args
    retTy' <- lowerTy' retTy
    let argctx = map (\(v,_,t) -> (castName v,t)) args'
    body' <- withVars argctx $ traverse lowerExprNoSusp body
    b' <- liftEM $ bindCDepBind args' (retTy', body')
    return $ CDef name b'

lowerUserFunc' :: CUserFunc FormatTy -> LM (CUserFunc VerusTy)
lowerUserFunc' (CUserFunc specName pubName secName pubBody secBody) = do
    pubBody' <- handleBody pubBody
    secBody' <- handleBody secBody
    return $ CUserFunc specName pubName secName pubBody' secBody'
    where
        handleBody b = do
            (args, (retTy, body)) <- liftEM $ unbindCDepBind b
            args' <- mapM lowerArg args
            retTy' <- lowerTy' retTy
            body' <- traverseCAExpr lowerTy' body
            liftEM $ bindCDepBind args' (retTy', body')


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
maybeLenOf (FBuf _ (Just flen)) = return $ Just $ lowerFLen flen
maybeLenOf (FHexConst s) = return $ Just $ CUsizeLit $ length s `div` 2
maybeLenOf _ = return Nothing

lowerTyDef :: String -> CTyDef FormatTy -> EM [(String, CTyDef (Maybe ConstUsize, VerusTy))]
lowerTyDef sname (CStructDef (CStruct name fields isVest isSecretParse isSecretSer)) = do
    let lowerField (n, t) = do
            t' <- lowerFieldTy t
            l <- maybeLenOf t
            return (n, (l, t'))
    fields' <- mapM lowerField fields
    return [(sname, CStructDef $ CStruct name fields' isVest isSecretParse isSecretSer)]
lowerTyDef sname (CEnumDef (CEnum name cases isVest execComb isSecret)) = do
    let lowerCase (n, t) = do
            tt' <- case t of
                Just t -> do
                    t' <- lowerFieldTy t
                    l <- maybeLenOf t
                    return $ Just (l, t')
                Nothing -> return Nothing
            return (n, tt')
    cases' <- mapM lowerCase $ M.assocs cases
    return [(sname, CEnumDef $ CEnum name (M.fromList cases') isVest execComb isSecret)]

lowerName :: (String, FLen, Int, BufSecrecy) -> EM (String, ConstUsize, Int, BufSecrecy)
lowerName (n, l, i, s) = do
    let l' = lowerFLen l
    return (n, l', i, s)



--------------------------------------------------------------------------------
-- Helper functions

vecU8 :: VerusTy
vecU8 = RTVec RTU8

arrayU8 :: ConstUsize -> VerusTy
arrayU8 n = RTArray RTU8 n

u8slice :: VerusTy
u8slice = RTRef RShared (RTSlice RTU8)

getSerializedTy :: LM VerusTy
getSerializedTy = lowerTy' $ FBuf BufPublic Nothing
