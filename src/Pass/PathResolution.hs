{-# LANGUAGE TemplateHaskell #-} 
{-# LANGUAGE GeneralizedNewtypeDeriving #-} 
{-# LANGUAGE FlexibleInstances #-} 
{-# LANGUAGE MultiParamTypeClasses #-} 
{-# LANGUAGE UndecidableInstances #-} 
{-# LANGUAGE FlexibleContexts #-} 
{-# LANGUAGE DataKinds #-} 
{-# LANGUAGE DeriveGeneric #-}
module PathResolution where
import AST
import Error.Diagnose.Position (Position)
import Control.Lens
import Control.Monad
import CmdArgs
import System.FilePath
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Except
import qualified TypingBase as T
import qualified Text.Parsec as P
import Error.Diagnose
import qualified Parse as P
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Unsafe
import Unbound.Generics.LocallyNameless.TH
import System.FilePath ((</>), takeFileName)
import System.IO
import Pretty
import Prettyprinter
import Data.IORef

builtinFuncs :: [String]
builtinFuncs = ["UNIT", "TRUE", "FALSE", "eq", "Some", "None", "andb", "length", "plus", "mult", "zero", "concat", "cipherlen", "pk_cipherlen", "vk", "dhpk", "enc_pk", "dh_combine", "sign", "pkdec", "dec", "vrfy", "mac", "mac_vrfy", "checknonce", "prf", "H", "is_group_elem", "crh"]

data PathType = 
    PTName
      | PTTy
      | PTFunc
      | PTLoc
      | PTDef
      | PTTbl
      | PTMod
      | PTCounter
      | PTPredicate
      deriving Eq

instance Show PathType where
    show PTName = "name"
    show PTTy = "type"
    show PTFunc = "function"
    show PTLoc = "locality"
    show PTDef = "def"
    show PTTbl = "table"
    show PTMod = "module"
    show PTCounter = "counter"
    show PTPredicate = "predicate"

data IsNameRO = IsRO | NotRO
    deriving Eq

data ResolveEnv = ResolveEnv { 
    _flags :: Flags,
    _includes :: S.Set String,
    _curPath :: ResolvedPath,
    _namePaths :: T.Map String ResolvedPath,
    _tyPaths :: T.Map String ResolvedPath,
    _funcPaths :: T.Map String ResolvedPath,
    _localityPaths :: T.Map String ResolvedPath,
    _defPaths :: T.Map String ResolvedPath,
    _tablePaths :: T.Map String ResolvedPath,
    _predPaths :: T.Map String ResolvedPath,
    _ctrPaths :: T.Map String ResolvedPath,
    _modPaths :: T.Map String (Bool, ResolvedPath), -- Bool is whether the module is bound
    _freshCtr :: IORef Integer
                             }

makeLenses ''ResolveEnv

newtype Resolve a = Resolve { unResolve :: ReaderT ResolveEnv (ExceptT () IO) a }
    deriving (Functor, Applicative, Monad, MonadReader ResolveEnv, MonadIO)

instance Fresh Resolve where
    fresh (Fn s _) = do
        r <- view freshCtr
        n <- liftIO $ readIORef r
        liftIO $ writeIORef r (n + 1)
        return $ (Fn s n)
    fresh nm@(Bn {}) = return nm

freshModVar :: String -> Resolve (Name ResolvedPath)
freshModVar s = do
    r <- view freshCtr
    i <- liftIO $ readIORef r
    liftIO $ writeIORef r (i + 1)
    return $ s2n $ "_MOD_" ++ s ++ show i

emptyResolveEnv :: Flags -> IO ResolveEnv
emptyResolveEnv f = do
    r <- newIORef 0
    return $ ResolveEnv f S.empty (PTop) [] [] [] [] [] [] [] [] [] r

runResolve :: Flags -> Resolve a -> IO (Either () a) 
runResolve f (Resolve k) = do
    e <- emptyResolveEnv f
    runExceptT $ runReaderT k e

resolveError :: Ignore Position -> String -> Resolve a
resolveError pos msg = do
    fn <- takeFileName <$> (view $ flags . fFilePath)
    fl <- takeDirectory <$> (view $ flags . fFilePath)
    f <- view $ flags . fFileContents
    let rep = Err Nothing msg [(unignore pos, This ("Resolution error: " ++ msg))] []
    let diag = addFile (addReport def rep) (fn) f  
    printDiagnostic stdout True True 4 defaultStyle diag 
    Resolve $ lift $ throwError () 

debug :: Doc ann -> Resolve ()
debug d = do
    b <- view $ flags . fDebug
    when b $ liftIO $ putStrLn $ show d

resolveDecls :: [Decl] -> Resolve [Decl]
resolveDecls [] = return []
resolveDecls (d:ds) = 
    case d^.val of
      DeclFun s bp -> do
          (b, a) <- unbind bp
          a' <- resolveAExpr a
          pth <- view curPath
          ds' <- local (over funcPaths $ T.insert s pth) $ resolveDecls ds
          let d' = Spanned (d^.spanOf) $ DeclFun s $ bind b a'
          return (d' : ds')
      DeclPredicate s bp -> do
          ((ps, xs), p) <- unbind bp
          p' <- resolveProp p
          pth <- view curPath
          ds' <- local (over predPaths $ T.insert s pth) $ resolveDecls ds
          let d' = Spanned (d^.spanOf) $ DeclPredicate s $ bind (ps, xs) p'
          return (d' : ds')
      DeclSMTOption s1 s2 -> do
          ds' <-  resolveDecls ds
          return (d : ds')
      DeclCounter s isloc -> do
          (is, loc) <- unbind isloc
          loc' <- resolveLocality (d^.spanOf) loc
          let d' = Spanned (d^.spanOf) $ DeclCounter s $ bind is loc'
          p <- view curPath
          ds' <- local (over ctrPaths $ T.insert s p) $ resolveDecls ds
          return (d' : ds')
      DeclName s ixs -> do
          (is, ndecl) <- unbind ixs
          ndecl' <- case ndecl of
                      DeclAbstractName -> return DeclAbstractName
                      DeclBaseName nt ls -> do
                          nt' <- resolveNameType nt
                          ls' <- mapM (resolveLocality (d^.spanOf)) ls
                          return $ DeclBaseName nt' ls'
                      DeclRO strictness b -> do
                          (xs, (a, req, nts, lem)) <- unbind b
                          a' <- resolveAExpr a
                          req' <- resolveProp req
                          nts' <- mapM resolveNameType nts
                          lem' <- resolveExpr lem
                          return $ DeclRO strictness $ bind xs (a', req', nts', lem')
          p <- view curPath
          let d' = Spanned (d^.spanOf) $ DeclName s $ bind is ndecl' 
          ds' <- local (over namePaths $ T.insert s p) $ resolveDecls ds
          return $ d' : ds'
      DeclDefHeader s isl -> do
          (is, l) <- unbind isl
          l' <- resolveLocality (d^.spanOf) l
          let d' = Spanned (d^.spanOf) $ DeclDefHeader s $ bind is l'
          p <- view curPath
          ds' <- local (over defPaths $ T.insert s p) $ resolveDecls ds
          return (d' : ds')
      DeclDef s ix -> do
          (is, (l, k)) <- unbind ix
          (xets, (mp, t, oe)) <- unbind k
          xets' <- forM xets $ \(x, et) -> do
              et' <- embed <$> resolveTy (unembed et)
              return (x, et')
          l' <- resolveLocality (d^.spanOf) l
          mp' <- traverse resolveProp mp
          t' <- resolveTy t
          oe' <- traverse resolveExpr oe
          let d' = Spanned (d^.spanOf) $ DeclDef s $ bind is (l', bind xets' (mp', t', oe'))
          p <- view curPath
          ds' <- local (over defPaths $ T.insert s p) $ resolveDecls ds
          return (d' : ds')
      DeclEnum  s xs -> do
          (is, vs) <- unbind xs
          vs' <- forM vs $ \(s, ot) -> do
              ot' <- traverse resolveTy ot
              return (s, ot')
          let d' = Spanned (d^.spanOf) $ DeclEnum s $ bind is vs'
          p <- view curPath
          ds' <- local (over tyPaths $ T.insert s p) $ 
                  local (over funcPaths $ T.insertMany $ map (\(x, _) -> (x, p)) vs) $ 
                   local (over funcPaths $ T.insertMany $ map (\(x, _) -> (x ++ "?", p)) vs) $ 
                      resolveDecls ds
          return (d' : ds')
      DeclInclude fn -> do
          p <- view curPath
          case p of
            PTop -> do
              incls <- view includes
              if S.member fn incls then resolveDecls ds else do
                  fl <- view flags
                  let fn' = (takeDirectory $ fl^.fFilePath) </> fn
                  s <- liftIO $ readFile fn'
                  pres <- liftIO $ P.runParserT P.parseFile () (takeFileName fn') s
                  case pres of
                    Left err -> resolveError (d^.spanOf) $ "parseError: " ++ show err
                    Right dcls -> local (over includes $ S.insert fn) $ resolveDecls (dcls ++ ds)
            _ -> resolveError (d^.spanOf) $ "include statements only allowed at top level"
      DeclStruct  s xs -> do
          (is, vs) <- unbind xs
          vs' <- forM vs $ \(s, ot) -> do
              ot' <- resolveTy ot
              return (s, ot')
          let d' = Spanned (d^.spanOf) $ DeclStruct s $ bind is vs'
          p <- view curPath
          ds' <- local (over tyPaths $ T.insert s p) $ 
              local (over funcPaths $ T.insert s p) $ 
                  local (over funcPaths $ T.insertMany $ map (\(x, _) -> (x, p)) vs) $ 
                      resolveDecls ds
          return (d' : ds')
      DeclTy s ot -> do
          ot' <- traverse resolveTy ot
          let d' = Spanned (d^.spanOf) $ DeclTy s ot'
          p <- view curPath
          ds' <- local (over tyPaths $ T.insert s p) $ resolveDecls ds
          return (d' : ds')
      DeclDetFunc s _ _ -> do
          let d' = d
          p <- view curPath
          ds' <- local (over funcPaths $ T.insert s p) $ resolveDecls ds
          return (d' : ds')
      DeclTable s t l -> do
          t' <- resolveTy t
          l' <- resolveLocality (d^.spanOf) l
          let d' = Spanned (d^.spanOf) $ DeclTable s t' l'
          p <- view curPath
          ds' <- local (over tablePaths $ T.insert s p) $ resolveDecls ds
          return (d' : ds')
      DeclCorr ils -> do
          (is, (l1, l2)) <- unbind ils
          l1' <- resolveLabel l1
          l2' <- resolveLabel l2
          let d' = Spanned (d^.spanOf) $ DeclCorr $ bind is (l1', l2')
          ds' <- resolveDecls ds
          return (d' : ds')
      DeclLocality s dc -> do
          dc' <- case dc of
                  Left i -> return $ Left i
                  Right pth -> do
                      pth' <- resolvePath (d^.spanOf) PTLoc pth
                      return $ Right pth'
          let d' = Spanned (d^.spanOf) $ DeclLocality s dc'
          p <- view curPath
          ds' <- local (over localityPaths $ T.insert s p) $ resolveDecls ds
          return (d' : ds')
      DeclModule s imt me mt -> do
          me' <- resolveModuleExp (d^.spanOf) me
          mt' <- traverse (resolveModuleExp (d^.spanOf)) mt
          let d' = Spanned (d^.spanOf) $ DeclModule s imt me' mt' 
          p <- view curPath
          ds' <- local (over modPaths $ T.insert s (False, p)) $ resolveDecls ds 
          return (d' : ds')

resolveModuleExp :: Ignore Position -> ModuleExp -> Resolve ModuleExp
resolveModuleExp pos me = 
    case me^.val of
      ModuleBody imt xs -> do
          (x, ds1) <- unbind xs
          ds1' <- local (set curPath (PPathVar OpenPathVar x)) $ resolveDecls ds1
          return $ Spanned (me^.spanOf) $ ModuleBody imt (bind x ds1') 
      ModuleVar p -> do
          p' <- resolvePath pos PTMod p 
          return $ Spanned (me^.spanOf) $ ModuleVar p'
      ModuleApp e1 p2 -> do
          e1' <- resolveModuleExp pos e1
          p2' <- resolvePath pos PTMod p2
          return $ Spanned (me^.spanOf) $ ModuleApp e1' p2'
      ModuleFun bdy -> do
          ((x, s, t), me) <- unbind bdy
          v <- freshModVar s
          t' <- resolveModuleExp pos (unembed t)
          me' <- local (over modPaths $ T.insert s (True, PPathVar (ClosedPathVar $ ignore s) v)) $ resolveModuleExp pos me 
          return $ Spanned (me^.spanOf) $ ModuleFun $ bind (v, s, embed t') me' 

resolveNoncePattern :: NoncePattern -> Resolve NoncePattern
resolveNoncePattern NPHere = return NPHere

resolveNameType :: NameType -> Resolve NameType
resolveNameType e = do
    e' <- go $ e^.val
    return $ Spanned (e^.spanOf) e'
        where
            go t =
                case t of
                  NT_DH -> return t
                  NT_Nonce -> return t
                  NT_Sig t -> NT_Sig <$> resolveTy t
                  NT_Enc t -> NT_Enc <$> resolveTy t
                  NT_PKE t -> NT_PKE <$> resolveTy t
                  NT_MAC t -> NT_MAC <$> resolveTy t
                  NT_StAEAD t xpr p np -> do
                      t' <- resolveTy t
                      (x, pr) <- unbind xpr
                      pr' <- resolveProp pr
                      p' <- resolvePath (e^.spanOf) PTCounter p
                      np' <- resolveNoncePattern np
                      return $ NT_StAEAD t' (bind x pr') p' np' 
                  NT_PRF xs -> do
                      xs' <- forM xs $ \(x, (y, z)) -> do
                          y' <- resolveAExpr y
                          z' <- resolveNameType z
                          return (x, (y', z'))
                      return $ NT_PRF xs'

resolveTy :: Ty -> Resolve Ty
resolveTy e = do
    e' <- go $ e^.val
    return $ Spanned (e^.spanOf) e'
        where
            go t = 
                case t of
                  TData l1 l2 s -> do
                      l1' <- resolveLabel l1
                      l2' <- resolveLabel l2
                      return $ TData l1' l2' s
                  TDataWithLength l a -> do
                      l' <- resolveLabel l
                      a' <- resolveAExpr a
                      return $ TDataWithLength l' a'
                  TRefined t s xp -> do
                      t' <- resolveTy t
                      (x, p) <- unbind xp
                      p' <- resolveProp p
                      return $ TRefined t' s $ bind x p'
                  TOption t -> TOption <$> resolveTy t
                  TConst p fs -> do
                      fs' <- mapM resolveFuncParam fs
                      p' <- resolvePath (e^.spanOf) PTTy p
                      return $ TConst p' fs'
                  TBool l -> TBool <$> resolveLabel l
                  TUnion t1 t2 -> liftM2 TUnion (resolveTy t1) (resolveTy t2)
                  TUnit -> return TUnit
                  TName ne -> TName <$> resolveNameExp ne
                  TVK ne -> TVK <$> resolveNameExp ne
                  TDH_PK ne -> TDH_PK <$> resolveNameExp ne
                  TEnc_PK ne -> TEnc_PK <$> resolveNameExp ne
                  TSS ne ne' -> liftM2 TSS (resolveNameExp ne) (resolveNameExp ne')
                  TAdmit -> return TAdmit
                  TExistsIdx xt -> do
                      (x, t) <- unbind xt
                      t' <- resolveTy t
                      return $ TExistsIdx $ bind x t'
                  TCase p t1 t2 -> do
                      p' <- resolveProp p
                      t1' <- resolveTy t1
                      t2' <- resolveTy t2
                      return $ TCase p' t1' t2'


resolveNameExp :: NameExp -> Resolve NameExp
resolveNameExp ne = 
    case ne^.val of
        NameConst s p oi -> do
            p' <- resolvePath (ne^.spanOf) PTName p
            oi' <- case oi of
                     Nothing -> return Nothing
                     Just (as, i) -> do
                         as' <- mapM resolveAExpr as
                         return $ Just (as', i)
            return $ Spanned (ne^.spanOf) $ NameConst s p' oi'
        PRFName ne1 s -> do
            ne1' <- resolveNameExp ne1
            return $ Spanned (ne^.spanOf) $ PRFName ne1' s

resolveFuncParam :: FuncParam -> Resolve FuncParam
resolveFuncParam f = 
    case f of
      ParamAExpr a -> ParamAExpr <$> resolveAExpr a
      ParamStr s -> return f
      ParamLbl l -> ParamLbl <$> resolveLabel l
      ParamTy l -> ParamTy <$> resolveTy l
      ParamName n -> ParamName <$> resolveNameExp n
      ParamIdx _ -> return f


resolvePath pos pt p = do
    p' <- resolvePath' pos pt p
    debug $ owlpretty "Resolved " <> owlpretty p <> owlpretty " to " <> owlpretty p'
    return p'

resolvePath' :: Ignore Position -> PathType -> Path -> Resolve Path
resolvePath' pos pt p = 
    case p of
      PRes _ -> return p
      PUnresolvedPath x xs -> do
          debug $ owlpretty "Resolving " <> owlpretty p
          mp <- view modPaths
          res <- case lookup x mp of
                  Just (b, p) -> do
                      let xs' = if b then xs else x:xs
                      return $ PRes $ go (Just p) (reverse xs')
                  Nothing -> do
                      return $ PRes $ go Nothing (reverse (x:xs))
          return res
      PUnresolvedVar s -> 
          if (pt == PTFunc) && (s `elem` builtinFuncs) then return (PRes $ PDot PTop s) else 
          if (pt == PTMod) then do
                           mp <- view modPaths
                           case lookup s mp of
                             Nothing -> resolveError pos $ "Unknown " ++ show pt ++ ": " ++ s
                             Just (b, p) -> do
                                 if b then return (PRes p) else return (PRes (PDot p s))
                           else
          do
              mp <- case pt of
                      PTName -> view namePaths
                      PTTy -> view tyPaths
                      PTFunc -> view funcPaths
                      PTLoc -> view localityPaths
                      PTPredicate -> view predPaths
                      PTDef -> view defPaths
                      PTTbl -> view tablePaths
                      PTCounter -> view ctrPaths
              case lookup s mp of
                Just p -> return $ PRes $ PDot p s
                Nothing -> resolveError pos $ "Unknown " ++ show pt ++ ": " ++ s
    where
        go :: Maybe ResolvedPath -> [String] -> ResolvedPath
        go p [] = case p of
                    Just v -> v
                    Nothing -> PTop
        go p (x:xs) = PDot (go p xs) x 

resolveEndpoint :: Ignore Position -> Endpoint -> Resolve Endpoint
resolveEndpoint pos l = 
    case l of
      Endpoint v -> return $ Endpoint v
      EndpointLocality loc -> EndpointLocality <$> resolveLocality pos loc

resolveLocality :: Ignore Position -> Locality -> Resolve Locality
resolveLocality pos l = 
    case l of
      Locality p is -> liftM2 Locality (resolvePath pos PTLoc p) (return is)

resolveLabel :: Label -> Resolve Label
resolveLabel l = 
    case l^.val of
      LName ne -> do
          ne' <- resolveNameExp ne
          return $ Spanned (l^.spanOf) $ LName ne'
      LZero -> return l
      LAdv -> return l
      LTop -> return l
      LJoin l1 l2 -> do
          l1' <- resolveLabel l1
          l2' <- resolveLabel l2
          return $ Spanned (l^.spanOf) $ LJoin l1' l2'
      LConst (TyLabelVar p) -> do
          p' <- resolvePath (l^.spanOf) PTTy p
          return $ Spanned (l^.spanOf) $ LConst (TyLabelVar p') 
      LRangeIdx xk -> do
          (x, k) <- unbind xk
          k' <- resolveLabel k
          return $ Spanned (l^.spanOf) $ LRangeIdx $ bind x k'

resolveAExpr :: AExpr -> Resolve AExpr
resolveAExpr a = 
    case a^.val of
      AEVar _ _ -> return a
      AEApp f ps as -> do
          f' <- resolvePath (a^.spanOf) PTFunc f
          ps' <- mapM resolveFuncParam ps
          as' <- mapM resolveAExpr as
          return $ Spanned (a^.spanOf) $ AEApp f' ps' as'
      AEHex _ -> return a
      AEPreimage p ps as -> do
          p' <- resolvePath (a^.spanOf) PTName p
          as' <- mapM resolveAExpr as
          return $ Spanned (a^.spanOf) $ AEPreimage p' ps as'
      AEGet ne -> do
          ne' <- resolveNameExp ne
          return $ Spanned (a^.spanOf) $ AEGet ne'
      AEGetEncPK ne -> do
          ne' <- resolveNameExp ne
          return $ Spanned (a^.spanOf) $ AEGetEncPK ne'
      AEGetVK ne -> do
          ne' <- resolveNameExp ne
          return $ Spanned (a^.spanOf) $ AEGetVK ne'
      AEPackIdx i a -> do
          a' <- resolveAExpr a
          return $ Spanned (a^.spanOf) $ AEPackIdx i a'
      AELenConst _ -> return a
      AEInt _ -> return a

resolveLemma :: Ignore Position -> BuiltinLemma -> Resolve BuiltinLemma
resolveLemma pos lem =
    case lem of
      LemmaCRH -> return lem
      LemmaConstant -> return lem
      LemmaDisjNotEq -> return lem
      LemmaCrossDH n1 n2 n3 -> do
          n1' <- resolveNameExp n1
          n2' <- resolveNameExp n2
          n3' <- resolveNameExp n3
          return $ LemmaCrossDH n1' n2' n3'


resolveCryptOp :: Ignore Position -> CryptOp -> Resolve CryptOp
resolveCryptOp pos cop = 
    case cop of
      CLemma l -> do
          l' <- resolveLemma pos l
          return $ CLemma l'
      CHash hints i -> do
          hints' <- forM hints $ \(p, is, as) -> do
              p' <- resolvePath pos PTName p
              as' <- mapM resolveAExpr as
              return (p', is, as')
          return $ CHash hints' i
      CAEnc -> return CAEnc
      CEncStAEAD p is -> do
          p' <- resolvePath pos PTCounter p
          return $ CEncStAEAD p' is
      CDecStAEAD -> return CDecStAEAD
      CADec -> return CADec
      CPKDec -> return CPKDec
      CPKEnc -> return CPKEnc
      CMac -> return CMac
      CMacVrfy -> return CMacVrfy
      CSign -> return CSign
      CSigVrfy -> return CSigVrfy
      CPRF x -> return $ CPRF x

resolveExpr :: Expr -> Resolve Expr
resolveExpr e = 
    case e^.val of
      ECrypt cop xs -> do
          cop' <- resolveCryptOp (e^.spanOf) cop
          xs' <- mapM resolveAExpr xs
          return $ Spanned (e^.spanOf) $ ECrypt cop' xs'
      EInput s xk -> do
          (x, k) <- unbind xk
          k' <- resolveExpr k
          return $ Spanned (e^.spanOf) $ EInput s $ bind x k'
      EOutput a oe -> do
          a' <- resolveAExpr a
          oe' <- traverse (resolveEndpoint (e^.spanOf)) oe
          return $ Spanned (e^.spanOf) $ EOutput a' oe'
      EBlock k -> do
          k' <- resolveExpr k
          return $ Spanned (e^.spanOf) $ EBlock k'
      ELet e1 ot anf s xk -> do
          e1' <- resolveExpr e1
          ot' <- traverse resolveTy ot
          (x, k) <- unbind xk
          k' <- resolveExpr k
          return $ Spanned (e^.spanOf) $ ELet e1' ot' anf s (bind x k')
      EUnionCase a s xk -> do
          a' <- resolveAExpr a
          (x, k) <- unbind xk
          k' <- resolveExpr k
          return $ Spanned (e^.spanOf) $ EUnionCase a' s (bind x k')
      EUnpack a xk -> do
          a' <- resolveAExpr a
          (x, k) <- unbind xk
          k' <- resolveExpr k
          return $ Spanned (e^.spanOf) $ EUnpack a' (bind x k')
      EChooseIdx ip ik -> do
          (i, k) <- unbind ik
          (i', p) <- unbind ip                         
          k' <- resolveExpr k
          p' <- resolveProp p
          return $ Spanned (e^.spanOf) $ EChooseIdx (bind i' p') (bind i k')
      EForallBV xpk -> do
          (x, k) <- unbind xpk
          k' <- resolveExpr k
          return $ Spanned (e^.spanOf) $ EForallBV (bind x k') 
      EForallIdx xpk -> do
          (x, k) <- unbind xpk
          k' <- resolveExpr k
          return $ Spanned (e^.spanOf) $ EForallIdx (bind x k')
      EIf a e1 e2 -> do
          a' <- resolveAExpr a
          e1' <- resolveExpr e1
          e2' <- resolveExpr e2
          return $ Spanned (e^.spanOf) $ EIf a' e1' e2'
      EGuard a e1 -> do
          a' <- resolveAExpr a
          e1' <- resolveExpr e1
          return $ Spanned (e^.spanOf) $ EGuard a' e1'
      ERet a -> do
          a' <- resolveAExpr a
          return $ Spanned (e^.spanOf) $ ERet a'
      EGetCtr p ps -> do
          p' <- resolvePath (e^.spanOf) PTCounter p
          return $ Spanned (e^.spanOf) $ EGetCtr p' ps
      EIncCtr p ps -> do
          p' <- resolvePath (e^.spanOf) PTCounter p
          return $ Spanned (e^.spanOf) $ EIncCtr p' ps
      EDebug dc -> do
          dc' <- resolveDebugCommand dc
          return $ Spanned (e^.spanOf) $ EDebug dc' 
      EAssert p -> do
          p' <- resolveProp p
          return $ Spanned (e^.spanOf) $ EAssert p'
      EAssume p -> do
          p' <- resolveProp p
          return $ Spanned (e^.spanOf) $ EAssume p'
      EAdmit -> return e
      ECall p is as -> do
          p' <- resolvePath (e^.spanOf) PTDef p
          as' <- mapM resolveAExpr as
          return $ Spanned (e^.spanOf) $ ECall p' is as' 
      ECase a cases -> do
          a' <- resolveExpr a
          cases' <- forM cases $ \(s, lr) -> do
              case lr of
                Left e1 -> do { e1' <- resolveExpr e1; return (s, Left e1') }
                Right (s1, xk) -> do { (x, k) <- unbind xk; k' <- resolveExpr k; return (s, Right (s1, bind x k') ) }
          return $ Spanned (e^.spanOf) $ ECase a' cases'
      EPCase p op k -> do
          p' <- resolveProp p
          op' <- traverse resolveProp op
          k' <- resolveExpr k
          return $ Spanned (e^.spanOf) $ EPCase p' op' k'
      ESetOption s1 s2 k -> do
          k' <- resolveExpr k
          return $ Spanned (e^.spanOf) $ ESetOption s1 s2 k'
      EFalseElim k -> do
          k' <- resolveExpr k
          return $ Spanned (e^.spanOf) $ EFalseElim k'
      ETLookup p a -> do
          p' <- resolvePath (e^.spanOf) PTTbl p
          a' <- resolveAExpr a
          return $ Spanned (e^.spanOf) $ ETLookup p' a'
      ETWrite p a1 a2 -> do
          p' <- resolvePath (e^.spanOf) PTTbl p
          a1' <- resolveAExpr a1
          a2' <- resolveAExpr a2
          return $ Spanned (e^.spanOf) $ ETWrite p' a1' a2'

resolveDebugCommand :: DebugCommand -> Resolve DebugCommand
resolveDebugCommand dc = 
    case dc of
      DebugPrintTyOf a -> DebugPrintTyOf <$> resolveAExpr a
      DebugPrintTy t -> DebugPrintTy <$> resolveTy t
      DebugPrintProp p -> DebugPrintProp <$> resolveProp p
      DebugPrintExpr e -> DebugPrintExpr <$> resolveExpr e
      DebugPrintLabel l -> DebugPrintLabel <$> resolveLabel l
      DebugResolveANF a -> DebugResolveANF <$> resolveAExpr a
      DebugPrint _ -> return dc
      DebugPrintTyContext _ -> return dc
      DebugPrintModules -> return dc


resolveProp :: Prop -> Resolve Prop
resolveProp p = 
    case p^.val of
      PTrue -> return p
      PFalse -> return p
      PAnd p1 p2 -> do
          p1' <- resolveProp p1
          p2' <- resolveProp p2
          return $ Spanned (p^.spanOf) $ PAnd p1' p2'
      POr p1 p2 -> do
          p1' <- resolveProp p1
          p2' <- resolveProp p2
          return $ Spanned (p^.spanOf) $ POr p1' p2'
      PNot p1 -> do
          p1' <- resolveProp p1
          return $ Spanned (p^.spanOf) $ PNot p1'
      PApp s is as -> do 
          as' <- mapM resolveAExpr as
          s' <- resolvePath (p^.spanOf) PTPredicate s
          return $ Spanned (p^.spanOf) $ PApp s' is as'
      PAADOf ne a -> do
          ne' <- resolveNameExp ne
          a' <- resolveAExpr a
          return $ Spanned (p^.spanOf) $ PAADOf ne' a'
      PLetIn a xp -> do
          a' <- resolveAExpr a
          (x, p) <- unbind xp
          p' <- resolveProp p
          return $ Spanned (p^.spanOf) $ PLetIn a' (bind x p')
      PEq a1 a2 -> do
          a1' <- resolveAExpr a1
          a2' <- resolveAExpr a2
          return $ Spanned (p^.spanOf) $ PEq a1' a2'
      PEqIdx _ _ -> return p
      PImpl p1 p2 -> do
          p1' <- resolveProp p1
          p2' <- resolveProp p2
          return $ Spanned (p^.spanOf) $ PImpl p1' p2'
      PFlow l1 l2 -> do
          l1' <- resolveLabel l1
          l2' <- resolveLabel l2
          return $ Spanned (p^.spanOf) $ PFlow l1' l2'
      PHappened pth is as -> do
          pth' <- resolvePath (p^.spanOf) PTDef pth
          as' <- mapM resolveAExpr as
          return $ Spanned (p^.spanOf) $ PHappened pth' is as'
      PRO a b i -> do
          a' <- resolveAExpr a
          b' <- resolveAExpr b
          return $ Spanned (p^.spanOf) $ PRO a' b' i
      PQuantIdx q ip -> do
          (i, p') <- unbind ip
          p''  <- resolveProp p'
          return $ Spanned (p^.spanOf) $ PQuantIdx q $ bind i p''
      PQuantBV q xp -> do
          (x, p') <- unbind xp
          p'' <- resolveProp p'
          return $ Spanned (p^.spanOf) $ PQuantBV q $ bind x p''


                                            
