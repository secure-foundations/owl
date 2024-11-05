{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuasiQuotes #-}
module ExtractionBase where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Data.Char
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
import Unbound.Generics.LocallyNameless.TH ()
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import AST
import CmdArgs
import System.IO
import qualified TypingBase as TB
import qualified SMTBase as SMT
import ConcreteAST
import Verus
import PrettyVerus
import Prettyprinter.Interpolate

newtype ExtractionMonad t a = ExtractionMonad (ReaderT (TB.Env SMT.SolverEnv) (StateT (Env t) (ExceptT ExtractionError IO)) a)
    deriving (Functor, Applicative, Monad, MonadState (Env t), MonadError ExtractionError, MonadIO, MonadReader (TB.Env SMT.SolverEnv))

runExtractionMonad :: (TB.Env SMT.SolverEnv) -> Env t -> ExtractionMonad t a -> IO (Either ExtractionError a)
runExtractionMonad tcEnv env (ExtractionMonad m) = runExceptT . evalStateT (runReaderT m tcEnv) $ env

liftCheck :: TB.Check' SMT.SolverEnv a -> ExtractionMonad t a
liftCheck c = do
    e <- ask
    o <- liftIO $ runExceptT $ runReaderT (TB.unCheck $ local (set TB.tcScope $ TB.TcGhost False) c) e
    case o of 
      Left s -> ExtractionMonad $ lift $ throwError $ ErrSomethingFailed $ "liftCheck error: "
      Right i -> return i



data Env t = Env {
        _flags :: Flags
    ,   _path :: String
    ,   _freshCtr :: Integer
    ,   _varCtx :: M.Map (CDataVar t) t
    ,   _funcs :: M.Map String ([FormatTy], FormatTy) -- function name -> (arg types, return type)
    ,   _owlUserFuncs :: M.Map String (TB.UserFunc, Maybe FormatTy) -- (return type (Just if needs extraction))
    ,   _memoKDF :: [(([NameKind], [AExpr]), (CDataVar t, t))]
    ,   _genVerusNameEnv :: M.Map String VNameData -- For GenVerus, need to store all the local names so we know their types
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
    | LiftedError ExtractionError
    | CantCastType String String String
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
    owlpretty (LiftedError e) =
        owlpretty "Lifted error:" <+> owlpretty e
    owlpretty (CantCastType v t1 t2) =
        owlpretty "Can't cast value" <+> owlpretty v <+> owlpretty "from type" <+> owlpretty t1 <+> owlpretty "to type" <+> owlpretty t2
    owlpretty (ErrSomethingFailed s) =
        owlpretty "Extraction failed with message:" <+> owlpretty s

data BufSecrecy = BufSecret | BufPublic

type LocalityName = String
type NameData = (String, FLen, Int, BufSecrecy) -- name, type, number of processID indices, whether should be SecretBuf or OwlBuf
type VNameData = (String, ConstUsize, Int, BufSecrecy)
type OwlDefData = (String, TB.Def)
data LocalityData nameData defData = LocalityData {
    _nLocIdxs :: Int, 
    _localNames :: [nameData], 
    _sharedNames :: [nameData], 
    _defs :: [defData], 
    _tables :: [(String, Ty)], 
    _counters :: [String]
} deriving Show
makeLenses ''LocalityData
data ExtractionData defData tyData nameData userFuncData = ExtractionData {
    _locMap :: M.Map LocalityName (LocalityData nameData defData),
    _presharedNames :: [(nameData, [LocalityName])],
    _pubKeys :: [nameData],
    _tyDefs :: [(String, tyData)],
    _userFuncs :: [userFuncData]
} deriving Show
makeLenses ''ExtractionData

type OwlExtractionData = ExtractionData OwlDefData TB.TyDef NameData (String, TB.UserFunc)
type OwlLocalityData = LocalityData NameData OwlDefData
type CFExtractionData = ExtractionData (Maybe (CDef FormatTy)) (CTyDef FormatTy) NameData (CUserFunc FormatTy)
type CRExtractionData = ExtractionData (Maybe (CDef VerusTy)) (CTyDef (Maybe ConstUsize, VerusTy)) VNameData (CUserFunc VerusTy)
type FormatLocalityData = LocalityData NameData (Maybe (CDef FormatTy))
type VerusLocalityData = LocalityData VNameData (Maybe (CDef VerusTy))


makeLenses ''Env

liftExtractionMonad :: ExtractionMonad t a -> ExtractionMonad t' a
liftExtractionMonad m = do
    tcEnv <- ask
    env' <- get
    let env = Env {
            _flags = env' ^. flags,
            _path = env' ^. path,
            _freshCtr = env' ^. freshCtr,
            _varCtx = M.empty,
            _funcs = env' ^. funcs,
            _owlUserFuncs = env' ^. owlUserFuncs,
            _memoKDF = [],
            _genVerusNameEnv = M.empty
        }
    o <- liftIO $ runExtractionMonad tcEnv env m
    case o of 
        Left s -> throwError $ LiftedError s
        Right i -> return i



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

initEnv :: Flags -> String -> [(String, TB.UserFunc)] -> Env t
initEnv flags path owlUserFuncs = Env flags path 0 M.empty M.empty (mkUFs owlUserFuncs) [] M.empty
    where
        mkUFs :: [(String, TB.UserFunc)] -> M.Map String (TB.UserFunc, Maybe FormatTy)
        mkUFs l = M.fromList $ map (\(s, uf) -> (s, (uf, Nothing))) l


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



unbindCDepBind :: (Alpha a, Alpha t, Typeable t) => CDepBind t a -> ExtractionMonad tt ([(CDataVar t, String, t)], a)
unbindCDepBind (CDPDone a) = return ([], a)
unbindCDepBind (CDPVar t s xd) = do
    (x, d) <- unbind xd 
    (xs, a) <- unbindCDepBind d 
    return ((x, s, t) : xs, a)

bindCDepBind :: (Alpha a, Alpha t, Typeable t) => [(CDataVar t, String, t)] -> a -> ExtractionMonad tt (CDepBind t a)
bindCDepBind [] a = return $ CDPDone a
bindCDepBind ((x, s, t):xs) a = do
    d <- bindCDepBind xs a
    return $ CDPVar t s (bind x d)

replacePrimes :: String -> String
replacePrimes = map (\c -> if c == '\'' || c == '.' then '_' else c)

execName :: String -> VerusName
execName owlName = "owl_" ++ replacePrimes owlName

-- cmpNameLifetime :: String -> String -> VerusName
-- cmpNameLifetime owlName lt = withLifetime ("owl_" ++ owlName) lt

specName :: String -> VerusName
specName owlName = "owlSpec_" ++ replacePrimes owlName

specNameOfExecName :: VerusName -> String
specNameOfExecName s = 
    if "owl_" `isPrefixOf` s then specName $ drop 4 s else error "specNameOf: not an owl name: " ++ s

fLenOfNameKind :: NameKind -> ExtractionMonad t FLen
fLenOfNameKind nk = do
    return $ FLNamed $ case nk of
        NK_KDF -> "kdfkey"
        NK_DH -> "group"
        NK_Enc -> "enckey"
        NK_PKE -> "pkekey"
        NK_Sig -> "sigkey"
        NK_MAC -> "mackey"
        NK_Nonce s -> s

fLenOfNameTy :: NameType -> ExtractionMonad t FLen
fLenOfNameTy nt = do
    nk <- liftCheck $ TB.getNameKind nt
    fLenOfNameKind nk

concreteLength :: ConstUsize -> ExtractionMonad t Int
concreteLength (CUsizeLit i) = return i
concreteLength (CUsizeConst s) = do
    l <- case s of
        "KDFKEY_SIZE"    -> return 32
        "GROUP_SIZE"     -> return 32
        "ENCKEY_SIZE"    -> return 32
        "MACKEY_SIZE"    -> return 64
        "NONCE_SIZE"     -> return 12
        "TAG_SIZE"       -> return 16
        "MACLEN_SIZE"    -> return 16
        "COUNTER_SIZE"   -> return 8
        "SIGNATURE_SIZE" -> return 64
        -- The below are for compatibility with old Owl and probably should be updated
        "VK_SIZE"        -> return 1219
        "SIGKEY_SIZE"    -> return 1219
        "PKEKEY_SIZE"    -> return 1219
        "PKE_PK_SIZE"    -> return 1219
        _ -> throwError $ UndefinedSymbol $ "concreteLength: unhandled length constant: " ++ s
    debugPrint $ "WARNING: using hardcoded concrete length: " ++ s ++ " = " ++ show l
    return l
concreteLength (CUsizePlus a b) = do
    a' <- concreteLength a
    b' <- concreteLength b
    return $ a' + b'

lowerLenConst :: String -> String
lowerLenConst s = map toUpper s ++ "_SIZE"

lowerFLen :: FLen -> ConstUsize
lowerFLen (FLConst n) = CUsizeLit n
lowerFLen (FLNamed n) = 
    let n' = lowerLenConst n in
    CUsizeConst n'
lowerFLen (FLPlus a b) = 
    let a' = lowerFLen a in
    let b' = lowerFLen b in
    CUsizePlus a' b'
lowerFLen (FLCipherlen a) = 
    let n' = lowerFLen a in
    CUsizePlus n' (CUsizeConst "TAG_SIZE")


hexStringToByteList :: String -> ExtractionMonad t (Doc ann)
hexStringToByteList [] = return $ pretty ""
hexStringToByteList (h1 : h2 : t) = do
    t' <- hexStringToByteList t
    return $ pretty "0x" <> pretty h1 <> pretty h2 <> pretty "u8," <+> t'
hexStringToByteList _ = throwError OddLengthHexConst

lookupNameKindAExprMap :: [(([NameKind], [AExpr]), a)] -> [NameKind] -> [AExpr] -> Maybe a
lookupNameKindAExprMap [] nks args = Nothing
lookupNameKindAExprMap (((lnks, largs), r) : tl) nks args =
    if all (uncurry (==)) (zip nks lnks) && all (uncurry aeq) (zip args largs)
    then Just r
    else lookupNameKindAExprMap tl nks args


lookupKdfCall :: [NameKind] -> [AExpr] -> ExtractionMonad t (Maybe (CDataVar t, t))
lookupKdfCall nks k = do
    hcs <- use memoKDF
    return $ lookupNameKindAExprMap hcs nks k


mkNestPattern :: [Doc ann] -> Doc ann
mkNestPattern l = 
        case l of
            [] -> pretty ""
            [x] -> x
            x:y:tl -> foldl (\acc v -> parens (acc <+> pretty "," <+> v)) (parens (x <> pretty "," <+> y)) tl 

nestOrdChoiceTy :: [Doc ann] -> Doc ann
nestOrdChoiceTy l = 
    [di|ord_choice_type!(#{hsep . punctuate comma $ l})|]
        -- case l of
        --     [] -> pretty ""
        --     [x] -> x
        --     x:y:tl -> foldl (\acc v -> [di|OrdChoice<#{acc}, #{v}>|]) [di|OrdChoice<#{x}, #{y}>|] tl 

nestOrdChoice :: [Doc ann] -> Doc ann
nestOrdChoice l = 
        [di|ord_choice!(#{hsep . punctuate comma $ l})|]
        -- case l of
        --     [] -> pretty ""
        --     [x] -> x
        --     x:y:tl -> foldl (\acc v -> [di|OrdChoice(#{acc}, #{v})|]) [di|OrdChoice(#{x}, #{y})|] tl 

-- injOrdChoice i l x macro prints the macro call for x in a list of length l at index i
injOrdChoice :: Int -> Int -> Doc ann -> Doc ann -> Doc ann
injOrdChoice i l x macro =
    let starstr = hsep . punctuate comma $ [if j == i then [di|#{x}|] else [di|*|] | j <- [0 .. l-1]] in
    [di|#{macro}(#{starstr})|]   

listIdxToInjPat :: Int -> Int -> Doc ann -> ExtractionMonad t (Doc ann)
listIdxToInjPat i l x = return $ injOrdChoice i l x [di|inj_ord_choice_pat!|]   

listIdxToInjResult :: Int -> Int -> Doc ann -> ExtractionMonad t (Doc ann)
listIdxToInjResult i l x = return $ injOrdChoice i l x [di|inj_ord_choice_result!|]   


-- -- listIdxToEitherPat i l x prints the right Either pattern for x in a list of length l at index i
-- listIdxToEitherPat :: Int -> Int -> Doc ann -> ExtractionMonad t (Doc ann)
-- listIdxToEitherPat i l x = do
--     let starstr = hsep . punctuate comma $ [if j == i then [di|#{x}|] else [di|*|] | j <- [0 .. l-1]]
--     return [di|inj_ord_choice_pat!(#{starstr})|]   
--     -- if i >= l then 
--     --     throwError $ ErrSomethingFailed $ "listIdxToEitherPat index error: " ++ show i ++ ", " ++ show l
--     -- else do
--     --     if l == 2 then
--     --         return $ if i == 0 then [di|Either::Left(#{x})|] else [di|Either::Right(#{x})|]
--     --     else if i == l - 1 then
--     --         return [di|Either::Right(#{x})|]
--     --     else do
--     --         x' <- listIdxToEitherPat i (l-1) x
--     --         return [di|Either::Left(#{x'})|]

withJustNothing :: (a -> ExtractionMonad t (Maybe b)) -> Maybe a -> ExtractionMonad t (Maybe (Maybe b))
withJustNothing f (Just x) = Just <$> f x
withJustNothing f Nothing = return (Just Nothing)

specCombTyOf' :: FormatTy -> ExtractionMonad t (Maybe (Doc ann))
specCombTyOf' (FBuf (Just flen)) = return $ Just [di|Bytes|]
specCombTyOf' (FBuf Nothing) = return $ Just [di|Tail|]
specCombTyOf' (FStruct _ fs) = do
    fs' <- mapM (specCombTyOf' . snd) fs
    case sequence fs' of
        Just fs'' -> do
            let nest = mkNestPattern fs''
            return $ Just [di|#{nest}|]
        Nothing -> return Nothing
specCombTyOf' (FEnum _ cs) = do
    cs' <- mapM (withJustNothing specCombTyOf' . snd) cs
    case sequence cs' of
        Just cs'' -> do
            let consts = [[di|Tag<U8, u8>|] | i <- [1 .. length cs'']]
            let cs''' = map (fromMaybe [di|Bytes|]) cs''
            let constCs = zipWith (\c i -> [di|(#{c}, #{i})|]) consts cs''' 
            let nest = nestOrdChoiceTy constCs
            return $ Just [di|#{nest}|]
        Nothing -> return Nothing
specCombTyOf' (FHexConst s) = do
    let l = length s `div` 2
    return $ Just [di|Tag<BytesN<#{l}>, Seq<u8>>|]
specCombTyOf' _ = return Nothing

specCombTyOf :: FormatTy -> ExtractionMonad t (Doc ann)
specCombTyOf = liftFromJust specCombTyOf'

execCombTyOf' :: FormatTy -> ExtractionMonad t (Maybe (Doc ann))
execCombTyOf' (FBuf (Just flen)) = return $ Just [di|Bytes|]
execCombTyOf' (FBuf Nothing) = return $ Just [di|Tail|]
execCombTyOf' (FStruct _ fs) = do
    fs' <- mapM (execCombTyOf' . snd) fs
    case sequence fs' of
        Just fs'' -> do
            let nest = mkNestPattern fs''
            return $ Just [di|#{nest}|]
        Nothing -> return Nothing
execCombTyOf' (FEnum _ cs) = do
    cs' <- mapM (withJustNothing execCombTyOf' . snd) cs
    case sequence cs' of
        Just cs'' -> do
            let consts = [[di|Tag<U8, u8>|] | i <- [1 .. length cs'']]
            let cs''' = map (fromMaybe [di|Bytes|]) cs''
            let constCs = zipWith (\c i -> [di|(#{c}, #{i})|]) consts cs''' 
            let nest = nestOrdChoiceTy constCs
            return $ Just [di|#{nest}|]
        Nothing -> return Nothing
execCombTyOf' (FHexConst s) = do
    let l = length s `div` 2
    return $ Just [di|Tag<BytesN<#{l}>, [u8; #{l}]>|]
execCombTyOf' _ = return Nothing

execCombTyOf :: FormatTy -> ExtractionMonad t (Doc ann)
execCombTyOf = liftFromJust execCombTyOf'

-- (combinator type, any constants that need to be defined)
specCombOf' :: String -> FormatTy -> ExtractionMonad t (Maybe (Doc ann, Doc ann))
specCombOf' _ (FBuf (Just flen)) = do
    l <- concreteLength $ lowerFLen flen
    return $ noconst [di|Bytes(#{l})|]
specCombOf' _ (FBuf Nothing) = return $ noconst [di|Tail|]
specCombOf' constSuffix (FStruct _ fs) = do
    fcs <- mapM (specCombOf' constSuffix . snd) fs
    case sequence fcs of
        Just fcs' -> do
            let (fs', consts) = unzip fcs'
            let nest = mkNestPattern fs'
            -- We don't return the consts here, since they would already have been
            -- returned and printed when the nested struct was defined
            return $ noconst [di|#{nest}|]
        Nothing -> return Nothing
specCombOf' constSuffix (FEnum _ cs) = do
    cs' <- mapM (withJustNothing (specCombOf' constSuffix) . snd) cs
    case sequence cs' of
        Just ccs'' -> do
            let cs'' = foldr (\opt cs -> 
                        case opt of
                            Just (c, const) -> Just c : cs
                            Nothing -> Nothing : cs
                    ) [] ccs''
            let consts = [[di|Tag::spec_new(U8, #{i})|] | i <- [1 .. length cs'']]
            let cs''' = map (fromMaybe [di|Bytes(0)|]) cs''
            let constCs = zipWith (\c i -> [di|(#{c}, #{i})|]) consts cs'''
            let nest = nestOrdChoice constCs
            return $ noconst [di|#{nest}|]
        Nothing -> return Nothing
specCombOf' constSuffix (FHexConst s) = do
    let l = length s `div` 2
    bl <- hexStringToByteList s
    let constSuffix' = map Data.Char.toUpper constSuffix
    let const = [di|spec const SPEC_BYTES_CONST_#{s}_#{constSuffix'}: Seq<u8> = seq![#{bl}];|]
    return $ Just ([di|Tag::spec_new(BytesN::<#{l}>, (SPEC_BYTES_CONST_#{s}_#{constSuffix'}))|], const)
specCombOf' _ _ = return Nothing

specCombOf :: String -> FormatTy -> ExtractionMonad t (Doc ann, Doc ann)
specCombOf s = liftFromJust (specCombOf' s)

-- (combinator type, any constants that need to be defined)
execCombOf' :: String -> FormatTy -> ExtractionMonad t (Maybe (Doc ann, Doc ann))
execCombOf' _ (FBuf (Just flen)) = do
    l <- concreteLength $ lowerFLen flen
    return $ noconst [di|Bytes(#{l})|]
execCombOf' _ (FBuf Nothing) = return $ noconst [di|Tail|]
execCombOf' constSuffix (FStruct _ fs) = do
    fcs <- mapM (execCombOf' constSuffix . snd) fs
    case sequence fcs of
        Just fcs' -> do
            let (fs', consts) = unzip fcs'
            let nest = mkNestPattern fs'
            -- We don't return the consts here, since they would already have been
            -- returned and printed when the nested struct was defined
            return $ noconst [di|#{nest}|]
        Nothing -> return Nothing
execCombOf' constSuffix (FEnum _ cs) = do
    cs' <- mapM (withJustNothing (specCombOf' constSuffix) . snd) cs
    case sequence cs' of
        Just ccs'' -> do
            let cs'' = foldr (\opt cs -> 
                        case opt of
                            Just (c, const) -> Just c : cs
                            Nothing -> Nothing : cs
                    ) [] ccs''
            let consts = [[di|Tag::new(U8, #{i})|] | i <- [1 .. length cs'']]
            let cs''' = map (fromMaybe [di|Bytes(0)|]) cs''
            let constCs = zipWith (\c i -> [di|(#{c}, #{i})|]) consts cs''' 
            let nest = nestOrdChoice constCs
            return $ noconst [di|#{nest}|]
        Nothing -> return Nothing
execCombOf' constSuffix (FHexConst s) = do
    bl <- hexStringToByteList s
    let l = length s `div` 2
    let constSuffix' = map Data.Char.toUpper constSuffix
    let const = [__di|
    exec const EXEC_BYTES_CONST_#{s}_#{constSuffix'}: [u8; #{l}] 
        ensures EXEC_BYTES_CONST_#{s}_#{constSuffix'}.view() == SPEC_BYTES_CONST_#{s}_#{constSuffix'} 
    {
        let arr: [u8; #{l}] = [#{bl}];
        assert(arr.view() == SPEC_BYTES_CONST_#{s}_#{constSuffix'});
        arr
    }
    |]
    return $ Just ([di|Tag::new(BytesN::<#{l}>, (EXEC_BYTES_CONST_#{s}_#{constSuffix'}))|], const)
execCombOf' _ _ = return Nothing

execCombOf :: String -> FormatTy -> ExtractionMonad t (Doc ann, Doc ann)
execCombOf s = liftFromJust (execCombOf' s)


execParsleyCombOf' :: String -> FormatTy -> ExtractionMonad t (Maybe ParsleyCombinator)
execParsleyCombOf' _ (FBuf (Just flen)) = do
    return $ Just $ PCBytes flen
execParsleyCombOf' _ (FBuf Nothing) = return $ Just $ PCTail
execParsleyCombOf' constSuffix (FHexConst s) = do
    let constSuffix' = map Data.Char.toUpper constSuffix
    let len = length s `div` 2
    return $ Just $ PCConstBytes len $ "EXEC_BYTES_CONST_" ++ s ++ "_" ++ constSuffix'
execParsleyCombOf' _ _ = return Nothing

execParsleyCombOf :: String -> FormatTy -> ExtractionMonad t ParsleyCombinator
execParsleyCombOf s = liftFromJust (execParsleyCombOf' s)

noconst :: a -> Maybe (a, Doc ann)
noconst x = Just (x, [di||])

liftFromJust :: (a -> ExtractionMonad t (Maybe b)) -> a -> ExtractionMonad t b
liftFromJust f x = do
    res <- f x
    case res of
        Just r -> return r
        Nothing -> throwError $ ErrSomethingFailed "liftFromJust failed"