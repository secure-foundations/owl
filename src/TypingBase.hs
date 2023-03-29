{-# LANGUAGE TemplateHaskell #-} 
{-# LANGUAGE GeneralizedNewtypeDeriving #-} 
{-# LANGUAGE FlexibleInstances #-} 
{-# LANGUAGE MultiParamTypeClasses #-} 
{-# LANGUAGE UndecidableInstances #-} 
{-# LANGUAGE FlexibleContexts #-} 
{-# LANGUAGE DataKinds #-} 
{-# LANGUAGE DeriveGeneric #-}
module TypingBase where
import AST
import qualified Data.Map.Strict as M
import Error.Diagnose
import qualified Data.Map.Ordered as OM
import qualified Data.Set as S
import Data.Maybe
import Data.IORef
import Control.Monad
import qualified Data.List as L
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Cont
import Prettyprinter
import Control.Lens
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name
import System.FilePath ((</>))
import System.IO


data Flags = Flags { 
    _fDebug :: Bool,
    _fLogSMT :: Bool,
    _fFileLoc :: String,
    _fFilename :: String,
    _fFileContents :: String
                   }

makeLenses ''Flags

data TcScope = 
      Ghost 
      | Def Locality

instance Pretty TcScope where
    pretty Ghost = pretty "ghost"
    pretty (Def l) = pretty "def" <> tupled [pretty l]

data IdxType = IdxSession | IdxPId | IdxGhost
    deriving Eq

instance Pretty IdxType where
    pretty IdxSession = pretty "IdxSession"
    pretty IdxPId = pretty "IdxPId"
    pretty IdxGhost = pretty "IdxGhost"

data DefIsAbstract = DefAbstract | DefConcrete
    deriving Eq

data Env = Env { 
    _envFlags :: Flags,
    _envIncludes :: S.Set String,
    _detFuncs :: M.Map String (Int, [FuncParam] -> [(AExpr, Ty)] -> Check TyX), 
    _distrs :: M.Map String (Int, [(AExpr, Ty)] -> Check TyX),
    _nameEnv :: OM.OMap String (Bind ([IdxVar], [IdxVar]) (Maybe (NameType, [Locality]))),
    _tyContext :: OM.OMap DataVar (Ignore String, Ty),
    _endpointContext :: S.Set EndpointVar,
    _tcScope :: TcScope,
    _tyDefs :: M.Map String TyDef,
    _randomOracle :: M.Map String (AExpr, NameType),
    _localAssumptions :: [SymAdvAssms],
    -- in scope atomic localities, eg "alice", "bob"; localities :: S.Set String -- ok
    _localities :: M.Map String Int,
    _defs :: M.Map String (DefIsAbstract, Bind ([IdxVar], [IdxVar]) FuncDef), -- First pair is whether 
    _labelVars :: S.Set String,
    _freshCtr :: IORef Integer,
    _tableEnv :: M.Map String (Ty, Locality),
    _flowDecls :: [(Label, Label)],
    _inScopeIndices ::  M.Map IdxVar IdxType
}


data FuncDef = FuncDef {
    _funcLocality :: Locality,
    _preReq_retTy :: Bind [(DataVar, Embed Ty)] (Prop, Ty)
}
    deriving (Show, Generic, Typeable)

instance Alpha FuncDef
instance Subst Idx FuncDef

data SymAdvAssms =
    SASec NameExp

data TyDef = 
    EnumDef (Bind [IdxVar] [(String, Maybe Ty)])
      | StructDef (Bind [IdxVar] [(String, Ty)])
      | TyAbbrev Ty
      | TyAbstract -- Public length

data TypeError =
    ErrWrongNameType NameExp String NameType
      | ErrBadArgs String [Ty] 
      | ErrWrongCases String AExpr (M.Map String (Maybe Ty)) (M.Map String (Either Expr (Ignore String, Bind DataVar Expr)))
      | ErrUnknownName String
      | ErrUnknownRO String
      | ErrUnknownPRF NameExp String
      | ErrAssertionFailed (Maybe String) Prop
      | ErrDuplicateVarName DataVar
      | ErrUnknownDistr String
      | ErrUnknownFunc String
      | ErrFlowCheck Label Label
      | ErrUnknownVar  DataVar
      | ErrUnknownType String
      | ErrLenAmbiguous Ty
      | ErrWrongLocality NameExp Locality (S.Set Locality)
      | ErrCannotProveSubtype Ty Ty
      | ErrNameStillAbstract String

instance Pretty (TypeError) where
    pretty (ErrWrongNameType n s nt) = 
        pretty "Wrong name type for " <> pretty n <> pretty ": expected " <> pretty s <> pretty ", got " <> pretty nt
    pretty (ErrBadArgs s ts) = 
        pretty "Bad argument types for " <> pretty s <> pretty ": got " <> pretty ts
    pretty (ErrUnknownRO s) = 
        pretty "Unknown random oracle value: " <> pretty s
    pretty (ErrUnknownPRF n s) = 
        pretty "Unknown prf value for " <> pretty n <> pretty ": " <> pretty s
    pretty (ErrDuplicateVarName s) = 
        pretty "Duplicate variable name: " <> pretty s
    pretty (ErrWrongCases s a expected actual) = 
        pretty "Wrong cases for " <> pretty s <> pretty " with "  <> pretty a  <> pretty " expected " <> pretty (M.keys expected) <> pretty " but got " <> pretty (M.keys actual)
    pretty (ErrAssertionFailed fn p) =
        pretty ": Assertion failed: " <> pretty p <> pretty " from " <> pretty fn
    pretty (ErrUnknownName s) =  
        pretty "Unknown name: " <> pretty s
    pretty (ErrUnknownDistr s) =  
        pretty "Unknown distr: " <> pretty s
    pretty (ErrUnknownFunc s) =  
        pretty "Unknown func: " <> pretty s
    pretty (ErrUnknownVar s) =  
        pretty "Unknown variable: " <> pretty s
    pretty (ErrUnknownType s) =  
        pretty "Unknown type name: " <> pretty s
    pretty (ErrFlowCheck l1 l2) =  
        pretty "Label " <> pretty l1 <> pretty " does not flow to " <> pretty l2
    pretty (ErrLenAmbiguous t) = 
        pretty "Type " <> pretty t <> pretty " has an ambiguous length"
    pretty (ErrCannotProveSubtype t1 t2) = 
        pretty "Cannot prove type " <> pretty t1 <> pretty " is a subtype of " <> pretty t2
    pretty (ErrWrongLocality n l ls) = 
        pretty "Locality of name " <> pretty n <> pretty " is not available to locality " <> pretty l
    pretty (ErrNameStillAbstract n) =
        pretty "Name" <+> pretty n <+> pretty "is abstract but needs to be concrete here"

instance Show TypeError where
    show s = show $ pretty s

newtype Check a = Check { unCheck :: ReaderT Env (ExceptT Env IO) a }
    deriving (Functor, Applicative, Monad, MonadReader Env, MonadIO)


makeLenses ''FuncDef

makeLenses ''Env

instance Fresh Check where
    fresh (Fn s _) = do
        r <- view freshCtr
        n <- liftIO $ readIORef r
        liftIO $ writeIORef r (n + 1)
        return $ (Fn s n)
    fresh nm@(Bn {}) = return nm

typeError :: Ignore Position -> String -> Check a
typeError pos msg = do
    fn <- view $ envFlags . fFilename
    fl <- view $ envFlags . fFileLoc
    f <- view $ envFlags . fFileContents
    tyc <- view tyContext
    let rep = Err Nothing msg [(unignore pos, This msg)] [Note $ show $ prettyTyContext tyc]
    let diag = addFile (addReport def rep) (fn) f  
    e <- ask
    printDiagnostic stdout True True 4 defaultStyle diag 
    Check $ lift $ throwError e

--instance (Monad m, MonadIO m, MonadReader Env m) => Fresh m where

freshVar :: Check String
freshVar = do
    r <- view freshCtr
    i <- liftIO $ readIORef r
    liftIO $ writeIORef r (i + 1)
    return $ ".x" ++ show i

freshIdx :: Check String
freshIdx = do
    r <- view freshCtr
    i <- liftIO $ readIORef r
    liftIO $ writeIORef r (i + 1)
    return $ ".i" ++ show i

freshLbl :: Check String
freshLbl = do
    r <- view freshCtr
    i <- liftIO $ readIORef r
    liftIO $ writeIORef r (i + 1)
    return $ ".l" ++ show i

-- Convenience functions for adding to the environment 

joinLbl :: Label -> Label -> Label
joinLbl l1 l2 = 
    if (l1^.val) `aeq` LZero then l2 else
    if (l2^.val) `aeq` LZero then l1 else 
    mkSpanned $ LJoin l1 l2


addVars :: [(DataVar, (Ignore String, Ty))] -> OM.OMap DataVar (Ignore String, Ty) -> OM.OMap DataVar (Ignore String, Ty)
addVars xs g = g OM.|<> (OM.fromList xs)
    
assert :: Ignore Position -> String -> Bool -> Check ()
assert pos m b = if b then return () else typeError pos m 

-- withVars xs k = add xs to the typing environment, continue as k with extended
-- envrionment

withVars :: [(DataVar, (Ignore String, Ty))] -> Check a -> Check a
withVars assocs k = do
    tyC <- view tyContext
    forM_ assocs $ \(x, _) -> 
        assert (ignore def) (show $ ErrDuplicateVarName x) $ not $ OM.member x tyC
    local (over tyContext $ addVars assocs) k


inferIdx :: Idx -> Check IdxType
inferIdx (IVar pos i) = do
    m <- view inScopeIndices
    tc <- view tcScope
    case M.lookup i m of
      Just t -> 
          case (tc, t) of
            (Def _, IdxGhost) ->  
                typeError pos $ "Index should be nonghost: " ++ show (pretty i) 
            _ -> return t
      Nothing -> typeError pos $ "Unknown index: " ++ show (pretty i)

checkIdx :: Idx -> Check ()
checkIdx i = do
    debug $ pretty "Checking index " <> pretty i
    _ <- inferIdx i
    return ()

checkIdxSession :: Idx -> Check ()
checkIdxSession i@(IVar pos _) = do
    it <- inferIdx i
    tc <- view tcScope
    case tc of
       Ghost -> assert pos (show $ pretty "Wrong index type: " <> pretty i <> pretty ", got " <> pretty it <+> pretty " expected Ghost or Session ID") $ it /= IdxPId
       Def _ ->  assert pos (show $ pretty "Wrong index type: " <> pretty i <> pretty ", got " <> pretty it <+> pretty " expected Session ID") $ it == IdxSession

checkIdxPId :: Idx -> Check ()
checkIdxPId i@(IVar pos _) = do
    it <- inferIdx i
    tc <- view tcScope
    case tc of
       Ghost -> assert pos (show $ pretty "Wrong index type: " <> pretty i <> pretty ", got " <> pretty it <+> pretty " expected Ghost or PId") $ it /= IdxSession
       Def _ -> assert pos (show $ pretty "Wrong index type: " <> pretty i <> pretty ", got " <> pretty it <+> pretty "expected PId") $ it == IdxPId

getNameInfo :: NameExp -> Check (Maybe (NameType, Maybe [Locality]))
getNameInfo ne = do
    debug $ pretty (unignore $ ne^.spanOf) <> pretty "Inferring name expression" <+> pretty ne 
    case ne^.val of 
     BaseName (vs1, vs2) n -> do
         nE <- view nameEnv
         tc <- view tcScope
         forM_ vs1 checkIdxSession
         forM_ vs2 checkIdxPId
         case OM.lookup n nE of
           Nothing -> typeError (ne^.spanOf) $ show $ ErrUnknownName n
           Just int -> do
               ((is, ps), ntLclsOpt) <- unbind int
               case ntLclsOpt of
                 Nothing -> return Nothing
                 Just (nt, lcls) -> do
                    when ((length vs1, length vs2) /= (length is, length ps)) $ 
                        typeError (ne^.spanOf) $ show $ pretty "Wrong index arity for name " <> pretty n <> pretty ": got " <> pretty (length vs1, length vs2) <> pretty ", expected " <> pretty (length is, length ps)
                    return $ substs (zip is vs1) $ substs (zip ps vs2) $ Just (nt, Just lcls)
     ROName s -> do
        ro <- view randomOracle
        case M.lookup s ro of
          Just (_, nt) -> return $ Just (nt, Nothing)
          Nothing -> typeError (ne^.spanOf) $ show $ ErrUnknownRO s
     PRFName n s -> do
         ntLclsOpt <- getNameInfo n
         case ntLclsOpt of
           Nothing -> typeError (ne^.spanOf) $ show $ ErrNameStillAbstract $ show $ pretty n
           Just (nt, _) -> 
            case nt^.val of
            NT_PRF xs -> 
                case L.find (\p -> fst p == s) xs of
                    Just (_, (_, nt')) -> return $ Just (nt, Nothing)
                    Nothing -> typeError (ne^.spanOf) $ show $ ErrUnknownPRF n s
            _ -> typeError (ne^.spanOf) $ show $ ErrWrongNameType n "prf" nt

getNameTypeOpt :: NameExp -> Check (Maybe NameType)
getNameTypeOpt ne = do
    ntLclsOpt <- getNameInfo ne
    case ntLclsOpt of
        Nothing -> return Nothing
        Just (nt, _) -> return $ Just nt

getNameType :: NameExp -> Check NameType
getNameType ne = do
    ntOpt <- getNameTypeOpt ne
    case ntOpt of
        Nothing -> typeError (ne^.spanOf) $ show $ ErrNameStillAbstract $ show $ pretty ne
        Just nt -> return nt


debug :: Doc ann -> Check ()
debug d = do
    b <- view $ envFlags . fDebug
    when b $ liftIO $ putStrLn $ show d

getTyDef :: Ignore Position -> String -> Check TyDef
getTyDef pos s = do
    tDs <- view tyDefs
    case M.lookup s tDs of
      Just td -> return td
      Nothing -> typeError pos $ "Unknown type variable: " ++ s 

-- AExpr's have unambiguous types, so can be inferred.


inferAExpr :: AExpr -> Check Ty
inferAExpr ae = do
    debug $ pretty (unignore $ ae^.spanOf) <> pretty "Inferring AExp" <+> pretty ae
    case ae^.val of
      AEVar _ x -> do 
        tC <- view tyContext
        case OM.lookup x tC of 
          Just (_, t) -> return t
          Nothing -> typeError (ae^.spanOf) $ show $ ErrUnknownVar x
      (AEApp f params args) -> do
        debug $ pretty "Inferring application: " <> pretty (unignore $ ae^.spanOf)
        ts <- mapM inferAExpr args
        fE <- view detFuncs
        case M.lookup f fE of 
          Just (ar, k) -> do
              assert (ae^.spanOf) (show $ pretty "Wrong arity for " <> pretty f) $ length ts == ar
              mkSpanned <$> k params (zip args ts)
              -- If the det func is found in our environment, use k to infer the
              -- return type.
          Nothing -> typeError (ae^.spanOf) (show $ ErrUnknownFunc f)
      (AEString s) -> return $ tData zeroLbl zeroLbl
      (AEInt i) -> return $ tData zeroLbl zeroLbl
      (AELenConst s) -> do
          assert (ae^.spanOf) ("Unknown length constant: " ++ s) $ s `elem` ["nonce", "DH", "enckey", "pkekey", "sigkey", "prfkey", "mackey", "signature", "vk", "maclen", "tag"]
          return $ tData zeroLbl zeroLbl
      (AEPackIdx idx@(IVar _ i) a) -> do
            _ <- local (set tcScope Ghost) $ inferIdx idx
            t <- inferAExpr a
            return $ mkSpanned $ TExistsIdx $ bind i t 
      (AEGet ne) -> do
          ts <- view tcScope
          ntLclsOpt <- getNameInfo ne
          case ntLclsOpt of
            Nothing -> typeError (ae^.spanOf) $ show $ ErrNameStillAbstract $ show $ pretty ne
            Just (_, ls) -> do
                ls' <- case ls of
                        Just x -> return x
                        Nothing -> typeError (ae^.spanOf) $ show $ pretty "Name not base: " <> pretty ne
                case ts of
                    Def curr_locality -> do
                        assert (ae^.spanOf) (show $ pretty "Wrong locality for " <> pretty ne <> pretty ": Got " <> pretty curr_locality) $
                            any (aeq curr_locality) ls'
                        return $ tName ne
                    _ -> return $ tName ne
      (AEGetEncPK ne) -> do
          case ne^.val of
            BaseName ([], []) _ -> return ()
            BaseName _ _ -> typeError (ae^.spanOf) $ "Cannot call get_encpk on indexed name"
            _ -> typeError (ae^.spanOf) $ "Cannot call get_encpk on random oracle or PRF name"
          ntLclsOpt <- getNameInfo ne
          case ntLclsOpt of
            Nothing -> typeError (ae^.spanOf) $ show $ ErrNameStillAbstract$ show $ pretty ne
            Just (nt, _) ->           
                case nt^.val of
                    NT_PKE _ -> return $ mkSpanned $ TEnc_PK ne
                    _ -> typeError (ae^.spanOf) $ show $ pretty "Expected encryption sk: " <> pretty ne
      (AEGetVK ne) -> do
          case ne^.val of
            BaseName ([], []) _ -> return ()
            BaseName _ _ -> typeError (ae^.spanOf) $ "Cannot call get_vk on indexed name"
            _ -> typeError (ae^.spanOf) $ "Cannot call get_vk on random oracle or PRF name"
          ntLclsOpt <- getNameInfo ne
          case ntLclsOpt of
            Nothing -> typeError (ae^.spanOf) $ show $ ErrNameStillAbstract $ show $ pretty ne
            Just (nt, _) ->          
                case nt^.val of
                    NT_Sig _ -> return $ mkSpanned $ TVK ne
                    _ -> typeError (ae^.spanOf) $ show $ pretty "Expected signature sk: " <> pretty ne

getEnumParams :: Ignore Position -> [FuncParam] -> Check ([Idx])
getEnumParams pos ps = forM ps $ \p -> 
     case p of
       ParamIdx i -> return i
       _ -> typeError pos $ "Wrong param on enum: " ++ show p

getStructParams :: Ignore Position -> [FuncParam] -> Check [Idx]
getStructParams pos ps =
    forM ps $ \p -> 
        case p of
            ParamIdx i -> return i
            _ -> typeError pos $ "Wrong param on struct: " ++ show p

extractEnum :: Ignore Position -> [FuncParam] -> String -> (Bind [IdxVar] [(String, Maybe Ty)]) -> Check ([(String, Maybe Ty)])
extractEnum pos ps s b = do
    idxs <- getEnumParams pos ps
    (is, bdy') <- unbind b
    assert (ignore def) (show $ pretty "Wrong index arity for enum " <> pretty s) $ length idxs == length is  
    let bdy = substs (zip is idxs) bdy'
    return bdy

extractStruct :: Ignore Position -> [FuncParam] -> String -> (Bind [IdxVar] [(String, Ty)]) -> Check [(String, Ty)]
extractStruct pos ps s b = do
    idxs <- getStructParams pos ps
    (is, xs') <- unbind b
    assert (ignore def) (show $ pretty "Wrong index arity for struct " <> pretty s <> pretty ": got " <> pretty idxs <> pretty " expected " <> pretty (length is)) $ length idxs == length is 
    return $ substs (zip is idxs) xs'



coveringLabel' :: Ty -> Check Label
coveringLabel' t = 
    case t^.val of
      (TData l _) -> return l
      (TDataWithLength l a) -> do
          t <- inferAExpr a
          l' <- coveringLabel' t
          return $ joinLbl l l'
      TBool l -> return l
      TUnit -> return $ zeroLbl
      (TRefined t1 _) -> coveringLabel' t1
      (TOption t) -> coveringLabel' t  
      (TName n) -> return $ nameLbl n
      (TVK n) -> return $ zeroLbl
      (TDH_PK n) -> return $ zeroLbl
      (TEnc_PK n) -> return $ zeroLbl
      (TSS n m) -> return $ joinLbl (nameLbl n) (nameLbl m) -- TODO: is this right? Definitely sound
      (TUnion t1 t2) -> do
          l1 <- coveringLabel' t1
          l2 <- coveringLabel' t2
          return $ joinLbl l1 l2
      (TVar s ps) -> do
          td <- getTyDef (t^.spanOf) s
          case td of
            EnumDef b -> do
                bdy <- extractEnum (t^.spanOf) ps s b
                ls <- mapM coveringLabel' $ catMaybes $ map snd bdy
                let l2 = foldr joinLbl zeroLbl ls
                return $ l2
            TyAbstract -> return $ joinLbl (varLbl s) advLbl
            TyAbbrev t -> coveringLabel' t
            StructDef ixs -> do
                xs <- extractStruct (t^.spanOf) ps s ixs
                ls <- forM xs $ \(_, t) -> coveringLabel' t
                return $ foldr joinLbl zeroLbl ls
      TAdmit -> return $ zeroLbl -- mostly a placeholder
      TCase _ t1 t2 -> do -- If the covering label is the same, then we just return it. Otherwise we fail
          l1 <- coveringLabel' t1
          l2 <- coveringLabel' t2
          if (l1 `aeq` l2) then return l1 else 
              typeError (t^.spanOf) $ show $ pretty "Difficult case for coveringLabel': TCase" <+> pretty l1 <+> pretty l2
      TExistsIdx xt -> do
          (x, t) <- unbind xt
          l <- local (over inScopeIndices $ M.insert x IdxGhost) $ coveringLabel' t
          let l1 = mkSpanned $ LRangeIdx $ bind x l
          return $ joinLbl advLbl l1

prettyTyContext :: OM.OMap DataVar (Ignore String, Ty) -> Doc ann
prettyTyContext e = vsep $ map (\(_, (x, t)) -> pretty (unignore x) <> pretty ":" <+> pretty t) (OM.assocs e)

prettyIndices :: M.Map IdxVar IdxType -> Doc ann
prettyIndices m = vsep $ map (\(i, it) -> pretty "index" <+> pretty i <> pretty ":" <+> pretty it) $ M.assocs m

prettyContext :: Env -> Doc ann
prettyContext e =
    vsep [prettyIndices (e^.inScopeIndices), prettyTyContext (e^.tyContext)]

-- Subroutines for type checking determistic functions. Currently only has
-- special cases for () (constant empty bitstring). Will contain code for
-- checking: sdec, pk, sign, vrfy 
