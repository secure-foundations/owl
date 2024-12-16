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

resolveLengthAnnot :: AExpr -> EM FLen
resolveLengthAnnot a = do
    case a^.val of
        AEInt i -> return $ FLConst i
        AELenConst s -> return $ FLNamed s
        AEApp p _ args -> do
            s <- concretifyPath p
            case (s, args) of
                ("plus", [a1, a2]) -> do
                    l1 <- resolveLengthAnnot a1
                    l2 <- resolveLengthAnnot a2
                    return $ FLPlus l1 l2
                ("cipherlen", [a1]) -> do
                    l1 <- resolveLengthAnnot a1
                    return $ FLCipherlen l1
                _ -> throwError $ ErrSomethingFailed $ "Unsupported length annotation: " ++ show (owlpretty a)
        _ -> throwError $ ErrSomethingFailed $ "Unsupported length annotation: " ++ show (owlpretty a)


concretifyTy :: Ty -> EM FormatTy
concretifyTy t = do
    -- debugPrint $ "Concretifying type:" ++ show (owlpretty t)
    case t^.val of
      TData _ _ _ -> return $ fPBuf Nothing
      TDataWithLength _ a -> do
          a' <- liftCheck $ TB.resolveANF a
          fPBuf . Just <$> resolveLengthAnnot a'
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
                (idxs, ts) <- unbind bnd
                TB.withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) idxs) $ do
                    cs <- forM ts $ \(s, ot) -> do
                        cot <- traverse concretifyTy ot
                        return (s, cot)
                    return $ FEnum pthName cs
            Just (TB.StructDef bnd) -> do
                (idxs, dp') <- unbind bnd
                TB.withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) idxs) $ do
                    let go dp = case dp of
                                DPDone _ -> return []
                                DPVar t s xres -> do
                                    c <- concretifyTy t
                                    (_, k) <- unbind xres
                                    ck <- go k
                                    return $ (s, c) : ck
                    s <- go dp'
                    return $ FStruct pthName s
      TConst _ _ -> throwError $ TypeError "invalid constant type in concretifyTy"
      TBool _ -> return $ FBool
      TUnit -> return $ FUnit
      TName ne -> formatTyOfNameExp ne
      TVK ne -> return $ fPBuf $ Just $ FLNamed "vk"
      TEnc_PK ne -> return $ fPBuf $ Just $ FLNamed "pke_pk"
      TDH_PK ne -> return $ fPBuf $ Just $ FLNamed "group"
      TSS ne1 ne2 -> return $ groupFormatTy BufSecret
      TAdmit -> throwError $ ErrSomethingFailed "Got admit type during concretization"
      TExistsIdx _ it -> do
          (i, t) <- unbind it
          TB.withIndices [(i, (ignore $ show i, IdxGhost))] $ concretifyTy t
      THexConst s -> return $ FHexConst s


hexConstType :: String -> FormatTy
hexConstType s = fPBuf $ Just $ FLConst $ length s `div` 2

groupFormatTy :: BufSecrecy -> FormatTy
groupFormatTy secrecy = FBuf secrecy $ Just $ FLNamed "group"

unifyFormatTy :: FormatTy -> FormatTy -> EM FormatTy
unifyFormatTy t1 t2 =
    case (t1, t2) of
        _ | t1 `aeq` t2 -> return t1        
        (FBuf s1 (Just l1), FBuf s2 (Just l2)) | s1 == s2 -> do
            l <- unifyFLen l1 l2
            return $ FBuf s1 $ Just l
        (FDummy, t2) -> return t2
        (t1, FDummy) -> return t1
        (FInt, FBuf BufPublic (Just (FLNamed "counter"))) -> return $ fPBuf $ Just $ FLNamed "counter"
        (FBuf BufPublic (Just (FLNamed "counter")), FInt) -> return $ fPBuf $ Just $ FLNamed "counter"
        (FOption t1', FOption t2') -> do
            t <- unifyFormatTy t1' t2'
            return $ FOption t
        (FStruct n1 fs1, FStruct n2 fs2) | n1 == n2 -> return t1
        (FEnum n1 fs1, FEnum n2 fs2) | n1 == n2 -> return t1
        (FHexConst s, FBuf BufPublic (Just flen)) -> do
            unifyFLen flen $ FLConst $ length s `div` 2
            return $ fPBuf $ Just flen
        (FBuf BufPublic (Just flen), FHexConst s) -> do
            unifyFLen flen $ FLConst $ length s `div` 2
            return $ fPBuf $ Just flen
        (FBuf s1 l1, FBuf s2 l2) -> do
            let s = joinSecrecy s1 s2
            l <- case (l1, l2) of
                (Just l1', Just l2') -> do
                    Just <$> unifyFLen l1' l2'
                (Just l1', Nothing) -> return $ Just l1'
                (Nothing, Just l2') -> return $ Just l2'
                (Nothing, Nothing) -> return Nothing
            return $ FBuf s l
        -- (FBuf BufSecret Nothing, FBuf BufSecret _) -> return $ FBuf BufSecret Nothing
        -- (FBuf BufSecret _, FBuf BufSecret Nothing) -> return $ FBuf BufSecret Nothing
        -- (FBuf BufSecret l1, FBuf BufPublic l2) -> do
        --     unifyFormatTy (FBuf BufSecret l1) (FBuf BufSecret l2)
        -- (FBuf BufPublic l1, FBuf BufSecret l2) -> do
        --     unifyFormatTy (FBuf BufSecret l1) (FBuf BufSecret l2)
        -- (FBuf BufPublic Nothing, _) -> return $ FBuf BufPublic Nothing
        -- (_, FBuf BufPublic Nothing) -> return $ FBuf BufPublic Nothing
        _ -> throwError $ ErrSomethingFailed $ "Could not unify format types " ++ show (owlpretty t1) ++ " and " ++ show (owlpretty t2)

unifyFLen :: FLen -> FLen -> EM FLen
unifyFLen l1 l2 =
    case (l1, l2) of
        (FLConst i1, FLConst i2) | i1 == i2 -> return $ FLConst i1
        (FLNamed s1, FLNamed s2) | s1 == s2 -> return $ FLNamed s1
        (FLPlus l1' l2', FLPlus l1'' l2'') -> do
            l1''' <- unifyFLen l1' l1''
            l2''' <- unifyFLen l2' l2''
            return $ FLPlus l1''' l2'''
        (FLCipherlen l1', FLCipherlen l2') -> do
            l <- unifyFLen l1' l2'
            return $ FLCipherlen l
        (FLConst _, FLNamed _) -> do
            cl1 <- concreteLength $ lowerFLen l1
            cl2 <- concreteLength $ lowerFLen l2
            if cl1 == cl2 then return l2
            else throwError $ ErrSomethingFailed $ "Could not unify lengths " ++ show l1 ++ " and " ++ show l2
        (FLNamed _, FLConst _) -> do
            cl1 <- concreteLength $ lowerFLen l1
            cl2 <- concreteLength $ lowerFLen l2
            if cl1 == cl2 then return l1
            else throwError $ ErrSomethingFailed $ "Could not unify lengths " ++ show l1 ++ " and " ++ show l2
        _ -> throwError $ ErrSomethingFailed $ "Could not unify lengths " ++ show l1 ++ " and " ++ show l2

formatTyOfNameExp :: NameExp -> EM FormatTy
formatTyOfNameExp ne = do
    case ne ^. val of
        NameConst _ _ _ -> do
            nt <- liftCheck $ TB.getNameType ne
            fl <- fLenOfNameTy nt
            sec <- secrecyOfNameTy nt
            return $ FBuf sec $ Just fl
        KDFName _ _ _ nks i _ _ -> do
            let nk = nks !! i
            sec <- secrecyOfNameKind nk
            FBuf sec . Just <$> fLenOfNameKind nk


concretifyNameExpLoc :: NameExp -> EM String -- Returns the flattened path
concretifyNameExpLoc n = do
    case n ^. val of
        NameConst _ p _ -> flattenPath p
        KDFName {} -> throwError $ UnsupportedNameExp n

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

flenOfFormatTy :: FormatTy -> Maybe FLen
flenOfFormatTy (FBuf _ o) = o
flenOfFormatTy FUnit = Just $ FLConst 0
flenOfFormatTy FGhost = Just $ FLConst 0
flenOfFormatTy FInt = Just $ FLConst 32 -- todo?
flenOfFormatTy _ = Nothing


bufcast :: CAExpr FormatTy -> FormatTy -> EM (CAExpr FormatTy, [CLetBinding])
bufcast ae t | secrecyOfFTy (ae ^. tty) == BufSecret && secrecyOfFTy t == BufPublic = do
    -- Need an explicit declassification here
    declassifiedBufName <- fresh $ s2n "declassified_buf"
    let decBufVar = Typed t $ CAVar (ignore "declassified_buf") declassifiedBufName
    tokName <- fresh $ s2n "declassify_tok"
    let tokVar = Typed FDeclassifyTok $ CAVar (ignore "declassify_tok") tokName
    let dop = DOControlFlow ae
    let doCFDeclassify = Typed t $ CRet $ Typed t $ CAApp "buf_declassify" [ae, tokVar]
    let declassifyExpr = Typed t $ CItreeDeclassify dop $ bind tokName doCFDeclassify
    let declassifyLetBinding = (declassifiedBufName, Nothing, declassifyExpr)
    return $ withLets [declassifyLetBinding] $ Typed t $ CAVar (ignore "declassified_buf") declassifiedBufName
bufcast ae t = do
    if (ae ^. tty) `aeq` t then return $ noLets ae
    else do
        let ae' = Typed t $ CACast ae t
        return $ noLets ae'



concretifyApp :: Path -> [FuncParam] -> [CAExpr FormatTy] -> EM (CAExpr FormatTy, [CLetBinding])
concretifyApp (PRes (PDot PTop f)) params args = do
    let argtys = map (^. tty) args
    case (f, argtys) of
        ("unit", _) -> return $ mkAppNoLets f FUnit
        ("true", _) -> return $ mkAppNoLets f FBool
        ("false", _) -> return$ mkAppNoLets f FBool
        ("eq", [x, y]) -> do
                unifyFormatTy x y
                let eqSecrecy = joinSecrecy (secrecyOfFTy x) (secrecyOfFTy y)
                case eqSecrecy of
                    BufSecret -> return $ mkAppNoLets "ct_eq" FBool
                    BufPublic -> return $ mkAppNoLets "eq" FBool
        ("Some", [x]) -> return $ mkAppNoLets f $ FOption x
        ("None", []) -> 
                case params of
                    [ParamTy owlT] -> do
                        t <- concretifyTy owlT
                        return $ mkAppNoLets f $ FOption t
                    _ -> do
                        -- This is probably fine, since some other branch should constrain the type
                        debugPrint "WARNING: Can't infer type of None, using dummy type"
                        return $ mkAppNoLets f $  FOption FDummy
        ("andb", [x, y]) -> return $ mkAppNoLets f FBool
        ("andp", [x, y]) -> return $ mkAppNoLets f FGhost
        ("notb", [x]) -> return $ mkAppNoLets f FBool
        ("length", [x]) -> return $ mkAppNoLets f FInt
        ("plus", [x, y]) -> return $ mkAppNoLets f FInt
        ("crh", [x]) -> return $ mkAppNoLets f $ fPBuf $ Just $ FLNamed "crh" -- TODO: secrecy for crh
        ("mult", [x, y]) -> return $ mkAppNoLets f FInt
        ("zero", []) -> return $ mkAppNoLets f FInt
        ("is_group_elem", [x]) -> return $ mkAppNoLets f FBool
        ("concat", [x, y]) -> do
                let concatLen = case (flenOfFormatTy x, flenOfFormatTy y) of
                        (Nothing, _) -> Nothing
                        (_, Nothing) -> Nothing
                        (Just x, Just y) -> Just $ FLPlus x y
                let concatSecrecy = joinSecrecy (secrecyOfFTy x) (secrecyOfFTy y)
                let concatName = case concatSecrecy of
                        BufSecret -> "secret_concat"
                        BufPublic -> "concat"
                return $ mkAppNoLets concatName $ FBuf concatSecrecy concatLen
        ("xor", [x, y]) -> do
            let xorSecrecy = joinSecrecy (secrecyOfFTy x) (secrecyOfFTy y)
            let xorName = case xorSecrecy of
                    BufSecret -> "secret_xor"
                    BufPublic -> "xor"
            return $ mkAppNoLets xorName $ FBuf xorSecrecy Nothing
            --   t <- unifyFormatTy x y
            --   case t of
            --     FBuf _ -> return t
            --     _ -> throwError $ ErrSomethingFailed $ "cannot extract xor " ++ show (owlpretty t)
        ("cipherlen", [x]) -> return $ mkAppNoLets f FInt
        ("pk_cipherlen", [x]) -> return $ mkAppNoLets f FInt
        ("vk", [x]) -> return $ mkAppNoLets f $ fPBuf $ Just $ FLNamed "vk"
        ("dhpk", [x]) -> return $ mkAppNoLets f $ groupFormatTy BufPublic
        ("enc_pk", [x]) -> return $ mkAppNoLets f $ fPBuf $ Just $ FLNamed "enc_pk"
        ("dh_combine", [x, y]) -> do
            -- We may not have this information at concretization time, but the typechecker tells us it is sound
            -- to extract dh_combine, so we don't check it here
            --   when (not $ (aeq x groupFormatTy) && (aeq y groupFormatTy)) $
            --       throwError $ ErrSomethingFailed $ "Cannot extract dh_combine"
            -- DH shared secrets should be secret buffers
            return $ mkAppNoLets f $ groupFormatTy BufSecret
        ("checknonce", [x, y]) -> return $ mkAppNoLets f FBool
        (p, _) -> do
            fs <- use funcs
            case fs M.!? p of
                Just (fargTys, retTy) -> do
                    when (length fargTys /= length args) $ throwError $ TypeError $ "Wrong number of arguments to function " ++ p
                    argsWithLets <- forM (zip fargTys args) $ \(t, a) -> do
                        -- if t == FGhost || (a ^. tty == FGhost) then return (a, [])
                        -- else do
                        unifyFormatTy t (a ^. tty) -- check types are compatible
                        bufcast a t
                    let (args', argsCastLets) = unzip argsWithLets
                    return $ withLets (concat argsCastLets) $ Typed retTy $ CAApp f args'
                Nothing -> do
                    oufs <- use owlUserFuncs
                    case oufs M.!? p of
                        Just (ufdef, rtyOpt) -> do
                            case rtyOpt of
                                Just rty -> return $ mkAppNoLets f rty
                                Nothing -> do
                                    rtUF <- rtyOfUserFunc p ufdef
                                    return $ mkAppNoLets f rtUF
                        Nothing -> do
                            throwError $ UndefinedSymbol $ show . owlpretty $ p
    where
        mkAppNoLets fname frty = noLets $ Typed frty $ CAApp fname args
concretifyApp _ _ _ = do
    throwError $ ErrSomethingFailed "Got bad path in concreteTyOfApp"

-- Special case: Owl lets us implicitly cast exec values into ghost, but we must make this
-- explicit in the concrete AST
ghostifyAppArgs :: Path -> [CAExpr FormatTy] -> EM [CAExpr FormatTy]
ghostifyAppArgs (PRes (PDot PTop p)) args = do
    fs <- use funcs
    case fs M.!? p of
        Just (argTys, _) -> ghostifyArgs argTys args 
        Nothing -> return args
ghostifyAppArgs _ args = return args

ghostifyArgs :: [FormatTy] -> [CAExpr FormatTy] -> EM [CAExpr FormatTy]
ghostifyArgs argTys args = do
    forM (zip argTys args) $ \(t, a) -> do
        if t == FGhost then return ghostUnit
        else return a


-- () in ghost
ghostUnit :: CAExpr FormatTy
ghostUnit = Typed FGhost $ CAApp "ghost_unit" []

-- none()
noneConcrete :: FormatTy -> CAExpr FormatTy
noneConcrete rett = Typed rett $ CAApp "None" []

concretifyAExprs :: [AExpr] -> EM ([CAExpr FormatTy], [CLetBinding])
concretifyAExprs aes = do
    (aes', lets) <- unzip <$> mapM concretifyAExpr aes
    return (aes', concat lets)

concretifyAExpr :: AExpr -> EM (CAExpr FormatTy, [CLetBinding])
concretifyAExpr a =
    case a^.val of
      AEGet n -> do
          t <- formatTyOfNameExp n
          s <- concretifyNameExpLoc n
          return $ noLets $ Typed t $ CAGet s
      AELenConst s -> return $ noLets $ Typed FInt $ CAInt $ FLNamed s
      AEInt i ->  return $ noLets $ Typed FInt $ CAInt $ FLConst i
      AEHex s -> return $ noLets $ Typed (hexConstType s) $ CAHexConst s
      AEKDF _ _ _ _ _ -> return $ noLets ghostUnit
      AEGetEncPK n -> do
          encPKFormatTy <- concretifyTy $ mkSpanned $ TEnc_PK n
          s <- concretifyNameExpLoc n
          return $ noLets $ Typed encPKFormatTy $ CAGetEncPK s
      AEGetVK n -> do
          vkFormatTy <- concretifyTy $ mkSpanned $ TVK n
          s <- concretifyNameExpLoc n
          return $ noLets $ Typed vkFormatTy $ CAGetVK s
      AEApp p ps aes -> do
          (vs, argLets) <- concretifyAExprs aes
          args <- ghostifyAppArgs p vs
          appWithLets <- concretifyApp p ps args
          return $ addLets argLets appWithLets
      AEVar s x -> do
          ot <- lookupVar $ castName x
          case ot of
            Nothing -> error "Unknown var"
            Just ct -> return $ noLets $ Typed ct $ CAVar s $ castName x

-- To enable CSE/memoization optimization, we allow concretifyExpr to
-- return a list of let-bindings that should be inserted before the current
-- expression being concretized. These get handled at `ELet`s.
type CLetBinding = (CDataVar FormatTy, Maybe AExpr, CExpr FormatTy)

noLets :: a -> (a, [CLetBinding])
noLets x = (x, [])

addLets :: [CLetBinding] -> (a, [CLetBinding]) -> (a, [CLetBinding])
addLets lets (x, lets') = (x, lets ++ lets')

withLets :: [CLetBinding] -> a -> (a, [CLetBinding])
withLets lets x = (x, lets)

exprFromLets :: [CLetBinding] -> CExpr FormatTy -> CExpr FormatTy
exprFromLets lets e = foldr (\(x, oanf, e') acc -> Typed (acc ^. tty) $ CLet e' oanf $ bind x acc) e lets

exprFromLets' :: (CExpr FormatTy, [CLetBinding]) -> CExpr FormatTy
exprFromLets' = uncurry $ flip exprFromLets

varsOfLets :: [CLetBinding] -> [(CDataVar FormatTy, FormatTy)]
varsOfLets = map (\(x, _, e) -> (x, e ^. tty))

concretifyExpr :: Expr -> EM (CExpr FormatTy, [CLetBinding])
concretifyExpr e = do
    -- debugPrint $ "Concretifying expr:"
    -- debugPrint $ show $ owlpretty e
    case e^.val of
      EInput _ xk -> do
          ((x, ep), k) <- unbind xk
          (k', lets) <- withVars [(castName x, fPBuf Nothing)] $ concretifyExpr k
          return $ withLets lets $ Typed (_tty k') $ CInput (fPBuf Nothing) $ bind (castName x, ep) k'
      EOutput a op -> do
          (c, clets) <- concretifyAExpr a
          return $ withLets clets $ Typed FUnit $ COutput c op
      ERet a -> do
        (v, vlets) <- concretifyAExpr a
        return $ withLets vlets $ Typed (_tty v) $ CRet v
      ELet e1 _ oanf s xk -> do
          (c1, c1Lets) <- concretifyExpr e1
          (x, k) <- unbind xk
          -- If the variable's Owl name is "_", and the expression is a ghost expression, we can skip the let
          case (name2String x, c1 ^. tty) of
            ("_", FGhost) -> concretifyExpr k
            _ -> do
                k' <- withVars ((castName x, _tty c1) : varsOfLets c1Lets) $ concretifyExpr k
                let k'' = exprFromLets' k'
                return $ noLets $ exprFromLets c1Lets $ Typed (_tty k'') $ CLet c1 oanf $ bind (castName x) k''
      ELetGhost _ s xk -> do
        (_,k) <- unbind xk
        concretifyExpr k
        --   (x, k) <- unbind xk
        --   k' <- withVars [(castName x, FGhost)] $ concretifyExpr k
        --   let k'' = exprFromLets' k'
        --   return $ noLets $ Typed (_tty k'') $ CLet (Typed FGhost (CRet ghostUnit)) Nothing $ bind (castName x) k''
      EBlock e b -> do
          (c, clets) <- concretifyExpr e
          return $ noLets $ exprFromLets clets $ Typed (_tty c) $ CBlock c
      EUnpack a _ ixk -> do
          (c, clets) <- concretifyAExpr a
          ((i, x), k) <- unbind ixk
          TB.withIndices [(i, (ignore $ show i, IdxGhost))] $ do
            k' <- withVars [(castName x, _tty c)] $ concretifyExpr k
            let k'' = exprFromLets' k'
            return $ withLets clets $ Typed (_tty k'') $ CLet (Typed (_tty c) (CRet c)) Nothing $ bind (castName x) k''
      EChooseBV _ _ xe -> do
          (x, e) <- unbind xe
          e' <- withVars [(castName x, FGhost)] $ concretifyExpr e
          let e'' = exprFromLets' e'
          return $ noLets $ Typed (_tty e'') $ CLet (Typed FGhost $ CRet ghostUnit) Nothing $ bind (castName x) e''
      EChooseIdx _ _ ie -> do
          (i, e) <- unbind ie
          TB.withIndices [(i, (ignore $ show i, IdxGhost))] $ do
            concretifyExpr e
      EIf a e1 e2 -> do
          (ca, calets) <- concretifyAExpr a
          c1 <- exprFromLets' <$> concretifyExpr e1
          c2 <- exprFromLets' <$> concretifyExpr e2
          t <- unifyFormatTy (_tty c1) (_tty c2)
          return $ withLets calets $ Typed t $ CIf ca c1 c2
      EForallBV _ _ -> return $ noLets $ Typed FGhost $ CRet ghostUnit
      EForallIdx _ _ -> return $ noLets $ Typed FGhost $ CRet ghostUnit
      EPackIdx _ e -> concretifyExpr e
      EGuard a e -> do
          (ca, calets) <- concretifyAExpr a
          ce <- exprFromLets' <$> concretifyExpr e
          return $ withLets calets $ Typed (_tty ce) $ CIf ca ce (Typed (_tty ce) $ CRet (noneConcrete $ _tty ce))
      EGetCtr p _ -> do
          s <- concretifyPath p
          return $ noLets $ Typed (fPBuf $ Just $ FLNamed "counter") $ CGetCtr s
      EIncCtr p _ -> do
          s <- concretifyPath p
          return $ noLets $ Typed FUnit $ CIncCtr s
      EDebug _ -> return $ noLets $ Typed FGhost $ CRet ghostUnit
      EAssert _ -> return $ noLets $ Typed FGhost $ CRet ghostUnit
      EAssume _ -> return $ noLets $ Typed FGhost $ CRet ghostUnit
      EAdmit -> return $ noLets $ Typed FGhost $ CRet ghostUnit
      ECrypt cop aes -> do
          (cs, argLets) <- concretifyAExprs aes
          -- resolvedArgs <- mapM resolveANF aes
          addLets argLets <$> concretifyCryptOp aes cop cs
      ECall p _ aes -> do
          s <- concretifyPath p
          (cs, argLets) <- concretifyAExprs aes
          (argtys, t) <- tySigOfCall p
          cs' <- ghostifyArgs argtys cs
          return $ withLets argLets $ Typed t $ CCall s t cs'
      EParse a t_target otherwiseCase xsk -> do
            (a', alets) <- concretifyAExpr a
            t_target' <- concretifyTy t_target
            otw' <- traverse concretifyExpr otherwiseCase
            let otw'' = fmap exprFromLets' otw'
            (xs, k) <- unbind xsk
            let xs' = map (\(x, s) -> (castName x, s)) xs
            (xtys, xtys') <- case t_target' of
                        FStruct _ fields -> return (zip (map fst xs') (map snd fields), zipWith (curry (\((a,b),c) -> (a,b,c))) xs' (map snd fields))
                        FEnum _ _ -> do
                            when (length xs' /= 1) $ throwError $ TypeError "Expected exactly one argument to EParse for enum"
                            return ([(head xs' ^. _1, t_target')], [(head xs' ^. _1, head xs' ^. _2, t_target')])
                        _ -> throwError $ TypeError $ "Expected datatype as target of EParse, got " ++ (show . owlpretty) t_target'
            pkind <- case a' ^. tty of
                        FBuf BufPublic _ -> return PFromBuf
                        FStruct _ _ -> return PFromDatatype
                        FEnum _ _ -> return PFromDatatype
                        FBuf BufSecret _ -> do
                            if hasSecParser t_target' then return PFromSecBuf
                            else throwError $ TypeError $ "Can't generate secret parser for data type: " ++ (show . owlpretty) t_target'
                        _ -> throwError $ TypeError $ "Expected buffer or datatype in EParse, got " ++ (show . owlpretty) (a' ^. tty)
            k' <- withVars xtys $ concretifyExpr k
            let k'' = exprFromLets' k'
            return $ withLets alets $ Typed (k'' ^. tty) $ CParse pkind a' t_target' otw'' $ bind xtys' k''
      ECase e otherwiseCase xsk -> do
            e' <- exprFromLets' <$> concretifyExpr e
            let startT = e' ^. tty
            casevalT <- case otherwiseCase of
                -- TODO: need to insert explicit declassification here
                Just (t, _) -> do
                    t' <- concretifyTy t
                    if t' `eqUpToSecrecy` startT then return startT else return t'
                Nothing -> case e' ^. tty of
                            FEnum _ _ -> return $ e' ^. tty
                            FOption _ -> return $ e' ^. tty
                            tt -> throwError $ TypeError $ "Expected enum or option type in ECase, got " ++ (show . owlpretty) tt
            let caseTyOf c = do
                    case casevalT of
                            FEnum _ cases -> do
                                case lookup c cases of
                                    Just (Just t) -> return t :: EM FormatTy
                                    _ -> throwError $ TypeError $ "attempted to take case " ++ c ++ " of enum type"
                            FOption t -> do
                                    if c == "Some" then return t else throwError $ TypeError $ "attempted to take case " ++ c ++ " of option type"
                            _ -> throwError $ ErrSomethingFailed "bad caseTyOf"
            cases' <- forM xsk $ \(c, o) ->
                case o of
                    Left k -> do
                        k' <- exprFromLets' <$> concretifyExpr k
                        return (c, Left k')
                    Right (_, xtk) -> do
                        (x, k) <- unbind xtk
                        let x' = castName x
                        caseTy <- caseTyOf c
                        k' <- withVars [(x', caseTy)] $ concretifyExpr k
                        let k'' = exprFromLets' k'
                        return (c, Right $ bind x' (caseTy, k''))
            avar <- fresh $ s2n "caseval"
            -- Assume the typechecker already checked that all branches return compatible types,
            -- so we just look at the first one to determine the return type
            let getCaseRt c = case c of
                            (_, Left k) -> k ^. tty
                            (_, Right xtk) -> 
                                let (_, (_, k)) = unsafeUnbind xtk in
                                k ^. tty
            let unifyCaseRt acc c = do
                    let ct = getCaseRt c
                    unifyFormatTy acc ct
            retTy <- foldM unifyCaseRt (getCaseRt . head $ cases') (tail cases')
            let caseStmt = Typed retTy $ CCase (Typed casevalT $ CAVar (ignore "caseval") avar) cases'
            (avar', parseAndCase) <- case otherwiseCase of
                Just (t, otw) -> do
                    -- debugPrint $ show (owlpretty e')
                    -- debugPrint $ show (owlpretty casevalT)
                    -- debugPrint $ show (owlpretty startT)
                    otw' <- exprFromLets' <$> concretifyExpr otw
                    avar' <- fresh $ s2n "parseval"
                    case casevalT of
                        -- Special case: sometimes, option types are given a type annotation, which 
                        -- shows up in this case, but we are parsing authentically from an option type
                        FOption _ -> return (avar, caseStmt)
                        _ | casevalT == startT -> return (avar, caseStmt)
                        -- We are parsing as part of the case, so we need PFromBuf
                        _ -> do 
                            let p = Typed retTy $
                                    CParse PFromBuf (Typed startT $ CAVar (ignore "parseval") avar') casevalT (Just otw') $
                                        bind [(avar, ignore "caseval", casevalT)] caseStmt
                            return (avar', p)
                Nothing -> return (avar, caseStmt)
            return $ noLets $ Typed retTy $ CLet e' Nothing $ bind avar' parseAndCase
      EPCase _ _ _ e -> concretifyExpr e
      ECorrCaseNameOf _ _ e -> concretifyExpr e
      EFalseElim e _ -> concretifyExpr e
      ETLookup p a -> do
          (c, clets) <- concretifyAExpr a
          t <- FOption <$> typeOfTable p
          s <- concretifyPath p
          return $ withLets clets $ Typed t $ CTLookup s c
      ETWrite p a1 a2 -> do
          (c1, c1lets) <- concretifyAExpr a1
          (c2, c2lets) <- concretifyAExpr a2
          s <- concretifyPath p
          return $ withLets (c1lets ++ c2lets) $ Typed FUnit $ CTWrite s c1 c2
      ESetOption _ _ e -> concretifyExpr e
      EOpenTyOf _ e -> concretifyExpr e

typeOfTable :: Path -> EM FormatTy
typeOfTable (PRes (PDot p n)) = do
    md <- liftCheck $ TB.openModule p
    case lookup n (TB._tableEnv md) of
      Nothing -> error "table not found"
      Just (t, _) -> concretifyTy t
typeOfTable _ = throwError $ TypeError "Unhandled case in typeOfTable"

tySigOfCall :: Path -> EM ([FormatTy], FormatTy)
tySigOfCall p = do
    bfdef <- liftCheck $ TB.getDefSpec p
    ((bi1, bi2), dspec) <- unbind bfdef
    let (TB.DefSpec _ _ db) = dspec
    TB.withIndices (map (\i -> (i, (ignore $ show i, IdxSession))) bi1 ++ map (\i -> (i, (ignore $ show i, IdxPId))) bi2)  $ go [] db
        where
            go argtys (DPVar t _ xk) = do
                t' <- concretifyTy t
                (_, k) <- unbind xk
                go (argtys ++ [t']) k
            go argtys (DPDone (_, t, _)) = do
                t' <- concretifyTy t
                return (argtys, t')


concretifyCryptOp :: [AExpr] -> CryptOp -> [CAExpr FormatTy] -> EM (CExpr FormatTy, [CLetBinding])
concretifyCryptOp resolvedArgs (CKDF _ _ nks nkidx) [salt, ikm, info] = do
    let nk = nks !! nkidx
    kdfLen <- kdfLenOf nks
    outLen <- fLenOfNameKind nk
    let kdfTy = fSBuf $ Just kdfLen
    let kdfOutTy = fSBuf $ Just outLen
    startOffset <- offsetOf nks nkidx
    endOffset <- offsetOf nks (nkidx + 1)
    vtopt <- lookupKdfCall nks resolvedArgs
    (kdfVar, lets) <- case vtopt of
        Just (var, varty) -> do
            -- debugPrint $ "Found memoized KDF call: " ++ show (owlpretty nks) ++ " " ++ show (owlpretty resolvedArgs)
            unifyFormatTy varty kdfTy
            return (var, [])
        Nothing -> do
            kdfVar <- do
                vn' <- fresh $ s2n "kdfval"
                fresh $ s2n (show vn')
            let doKdf = Typed kdfTy $ CRet $ Typed kdfTy $ CAApp "kdf" [Typed FInt (CAInt kdfLen), salt, ikm, info]
            let doKdfLetBinding = (kdfVar, Nothing, doKdf)
            memoKDF %= (:) ((nks, resolvedArgs), (kdfVar, kdfTy))
            return $ (kdfVar, [doKdfLetBinding])
    let doSlice = Typed kdfOutTy $ CRet $ Typed kdfOutTy $ 
            CAApp "subrange" [Typed kdfTy $ CAVar (ignore . show $ kdfVar) kdfVar, Typed FInt (CAInt startOffset), Typed FInt (CAInt endOffset)]
    sec <- secrecyOfNameKind nk
    case sec of
        BufSecret -> return $ withLets lets doSlice
        BufPublic -> do
            sliceVar <- fresh $ s2n "kdf_slice"
            let actualOutTy = fPBuf $ Just outLen
            let dop = DOControlFlow $ Typed kdfOutTy $ CAVar (ignore "kdf_slice") sliceVar
            return $ withLets lets $ Typed actualOutTy $ CItreeDeclassify dop $ bind sliceVar doSlice
    -- return $ noLets $ Typed outTy $ CLet doKdf Nothing $ bind kdfVar doSlice
    where
        kdfLenOf nks = foldl' FLPlus (FLConst 0) <$> mapM fLenOfNameKind nks
        offsetOf nks idx = kdfLenOf $ take idx nks
concretifyCryptOp _ (CLemma _) cs = return $ noLets $ Typed FGhost $ CRet ghostUnit
concretifyCryptOp _ CAEnc [k, x] = do
    let t = case x ^. tty of
              FBuf BufSecret (Just fl) -> FBuf BufPublic $ Just $ FLCipherlen fl
              _ -> FBuf BufPublic Nothing
    coinsName <- fresh $ s2n "coins"
    let sampFLen = FLNamed "nonce"
    let coinsVar = Typed (fSBuf $ Just sampFLen) $ CAVar (ignore "coins") coinsName
    let doEnc = Typed t $ CRet $ Typed t $ CAApp "enc" [k, x, coinsVar]
    return $ noLets $ Typed t $ CSample sampFLen (fSBuf $ Just sampFLen) $ bind coinsName doEnc
concretifyCryptOp _ CADec [k, c] = do
    let plaintextT = FOption $ fSBuf Nothing
    tokName <- fresh $ s2n "declassify_tok"
    let tokVar = Typed FDeclassifyTok $ CAVar (ignore "declassify_tok") tokName
    let dop = DOADec (k, c)
    let doDec = Typed plaintextT $ CRet $ Typed plaintextT $ CAApp "dec" [k, c, tokVar]
    return $ noLets $ Typed plaintextT $ CItreeDeclassify dop $ bind tokName doDec
concretifyCryptOp _ (CEncStAEAD np _ xpat) [k, x, aad] = do
    (patx, patbody) <- unbind xpat
    nonce <- concretifyPath np
    let t = case x ^. tty of
            FBuf BufSecret (Just fl) -> FBuf BufPublic $ Just $ FLCipherlen fl
            _ -> FBuf BufPublic Nothing
    -- return $ noLets $ Typed t $ CRet $ Typed t $ CAApp "enc_st_aead" [k, x, Typed FInt $ CACounter nonce, aad]
    ctrVar <- fresh $ s2n nonce
    let ctrTy = fSBuf $ Just $ FLNamed "counter"
    let getCtr = (ctrVar, Nothing, Typed ctrTy $ CGetCtr nonce)
    incVar <- fresh $ s2n "_"
    let incCtr = (incVar, Nothing, Typed FUnit $ CIncCtr nonce)
    let getInc = [getCtr, incCtr]
    (ivVar, mkIv, ivLets) <- case patbody ^. val of
        AEVar _ patx' | patx `aeq` patx' -> return (CAVar (ignore nonce) ctrVar, [], [])
        _ -> do 
            let patbodySubst = subst patx (mkSpanned $ AEVar (ignore nonce) (castName ctrVar)) patbody
            (iv, ivLets) <- withVars [(castName ctrVar, ctrTy)] $ concretifyAExpr patbodySubst
            let mkIv = [(castName patx, Nothing, Typed (iv ^. tty) $ CRet iv)]
            return (CAVar (ignore $ name2String patx) $ castName patx, mkIv, ivLets)
    return $ withLets (getInc ++ ivLets ++ mkIv) $ Typed t $ CRet $ Typed t $ CAApp "enc_st_aead" [k, x, Typed ctrTy $ ivVar, aad]
concretifyCryptOp _ CDecStAEAD [k, c, aad, nonce] = do
    let plaintextT = FOption $ fSBuf Nothing
    tokName <- fresh $ s2n "declassify_tok"
    let tokVar = Typed FDeclassifyTok $ CAVar (ignore "declassify_tok") tokName
    let dop = DOStAeadDec (k, c, nonce, aad)
    let doAeadDec = Typed plaintextT $ CRet $ Typed plaintextT $ CAApp "dec_st_aead" [k, c, nonce, aad, tokVar]
    return $ noLets $ Typed plaintextT $ CItreeDeclassify dop $ bind tokName doAeadDec
-- concretifyCryptOp _ CPKEnc [k, x] = do
--     let t = FBuf Nothing
--     return $ noLets $ Typed t $ CRet $ Typed t $ CAApp "pkenc" [k, x]
-- concretifyCryptOp _ CPKDec [k, x] = do
--     let t = FOption $ FBuf Nothing
--     return $ noLets $ Typed t $ CRet $ Typed t $ CAApp "pkdec" [k, x]
-- concretifyCryptOp _ CMac [k, x] = do
--     let t = FBuf $ Just $ FLNamed "maclen"
--     return $ noLets $ Typed t $ CRet $ Typed t $ CAApp "mac" [k, x]
-- concretifyCryptOp _ CMacVrfy [k, x, v] = do
--     let t = FOption $ FBuf Nothing
--     return $ noLets $ Typed t $ CRet $ Typed t $ CAApp "mac_vrfy" [k, x, v]
concretifyCryptOp _ CSign [k, x] = do
    let t = fPBuf $ Just $ FLNamed "signature"
    return $ noLets $ Typed t $ CRet $ Typed t $ CAApp "sign" [k, x]
concretifyCryptOp _ CSigVrfy [k, x, v] = do
    let plaintextT = FOption $ fSBuf Nothing
    tokName <- fresh $ s2n "declassify_tok"
    let tokVar = Typed FDeclassifyTok $ CAVar (ignore "declassify_tok") tokName
    let dop = DOSigVrfy (k, x, v)
    let doSigVrfy = Typed plaintextT $ CRet $ Typed plaintextT $ CAApp "vrfy" [k, x, v, tokVar]
    return $ noLets $ Typed plaintextT $ CItreeDeclassify dop $ bind tokName doSigVrfy
concretifyCryptOp _ cop cargs = throwError $ TypeError $
    "Got bad crypt op during concretization: " ++ show (owlpretty cop) ++ ", args: " ++ show (tupled . map owlpretty $ cargs)


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
    debugLog $ "Concretifying def: " ++ defName
    let ((sids, pids), dspec) = unsafeUnbind bd
    when (length sids > 1) $ throwError $ DefWithTooManySids defName
    ores <- 
        TB.withIndices (map (\i -> (i, (ignore $ show i, IdxSession))) sids ++ map (\i -> (i, (ignore $ show i, IdxPId))) pids) $ do
        withDepBind (dspec^.TB.preReq_retTy_body) $ \xts (p, retT, oexpr) ->  do
            when (not $ p `aeq` pTrue) $ throwError $ ErrSomethingFailed "Attempting to extract def with nontrivial prerequisite"
            -- cretT <- concretifyTy retT
            case oexpr of
                Nothing -> do
                    cretT <- concretifyTy retT
                    return $ Just (cretT, Nothing)
                Just e -> do
                    ce <- exprFromLets' <$> concretifyExpr e
                    let cretT = ce ^. tty
                    --   debugPrint . show . owlpretty $ defName
                    --   debugPrint . show . owlpretty $ ce
                    return $ Just (cretT, Just ce)
    case ores of
        Nothing -> return Nothing
        Just res -> return $ Just $ CDef defName res


userFuncArgTy :: FormatTy
userFuncArgTy = fPBuf Nothing

concretifyUserFunc' :: String -> TB.UserFunc -> EM (Maybe (CUserFunc FormatTy), FormatTy)
concretifyUserFunc' ufName (TB.FunDef bd) = do
    ((_, args), body) <- unbind bd
    let argstys = zip (map castName args) (repeat userFuncArgTy)
    (body', bodyLets) <- withVars argstys $ concretifyAExpr body
    when (not $ null bodyLets) $ throwError $ ErrSomethingFailed "User function body should not have lets"
    let rty = body' ^. tty
    let bindArgs = map (\(a,t) -> (a, show a, t)) argstys
    bd' <- bindCDepBind bindArgs (rty, body')
    return $ (Just $ CUserFunc ufName bd', rty)
concretifyUserFunc' ufName (TB.EnumTest caseName enumName) = do
    return (Nothing, FBool)
concretifyUserFunc' ufName uf = do
    throwError $ ErrSomethingFailed $ "Unsupported user function: " ++ ufName ++ ": " ++ show (owlpretty uf)

concretifyUserFunc :: String -> TB.UserFunc -> EM (Maybe (CUserFunc FormatTy))
concretifyUserFunc ufName uf = do
    (uf', _) <- concretifyUserFunc' ufName uf
    return uf'

rtyOfUserFunc :: String -> TB.UserFunc -> EM FormatTy
rtyOfUserFunc ufName uf = do
    (_, rty) <- concretifyUserFunc' ufName uf
    oufs <- use owlUserFuncs
    owlUserFuncs %= M.insert ufName (uf, Just rty)
    return rty


typeIsVest :: FormatTy -> Bool
typeIsVest (FStruct _ fs) = False -- all (typeIsVest . snd) fs
typeIsVest (FEnum _ cs) = False -- all (maybe True typeIsVest . snd) cs 
typeIsVest FGhost = False
typeIsVest FBool = False
typeIsVest (FOption t) = False
typeIsVest _ = True

concretifyTyDef :: String -> TB.TyDef -> EM (Maybe (CTyDef FormatTy))
concretifyTyDef tname (TB.TyAbstract) = return Nothing
concretifyTyDef tname (TB.TyAbbrev t) = return Nothing -- TODO: need to keep track of aliases
concretifyTyDef tname (TB.EnumDef bnd) = do
    debugLog $ "Concretifying enum: " ++ tname
    (idxs, ts) <- unbind bnd
    TB.withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) idxs) $ do
        cs <- forM ts $ \(s, ot) -> do
            cot <- traverse concretifyTy ot
            return (s, cot)
        let isVest = all (maybe True typeIsVest . snd) cs
        -- We generate the exec combinator here, so that we can use it in
        -- GenVerus where format types have been erased
        (execComb, _) <- execCombOf tname (FEnum tname cs)
        return $ Just $ CEnumDef (CEnum tname (M.fromList cs) isVest (show execComb))
concretifyTyDef tname (TB.StructDef bnd) = do 
    debugLog $ "Concretifying struct: " ++ tname
    (idxs, dp) <- unbind bnd
    TB.withIndices (map (\i -> (i, (ignore $ show i, IdxGhost))) idxs) $ do
        let go dp = case dp of
                    DPDone _ -> return []
                    DPVar t s xres -> do
                        c <- concretifyTy t
                        (_, k) <- unbind xres
                        ck <- go k
                        return $ (s, c) : ck
        s <- go dp
        let isVest = all (typeIsVest . snd) s
        let isSecret = all (hasSecParser . snd) s
        return $ Just $ CStructDef (CStruct tname s isVest isSecret)


setupEnv :: [(String, TB.TyDef)] -> EM ()
setupEnv [] = return ()
setupEnv ((tname, td):tydefs) = do
    tdef <- concretifyTyDef tname td
    case tdef of
        Nothing -> return ()
        Just (CEnumDef (CEnum _ cases _  _)) -> do
            -- We only have case constructors for each case, since enum projectors are replaced by the `case` statement
            let mkCase (cname, cty) = do
                    let argTys = case cty of
                            Just t -> [t]
                            Nothing -> []
                    let rty = FEnum tname $ M.assocs cases
                    funcs %= M.insert cname (argTys, rty)
            mapM_ mkCase (M.assocs cases)
        Just (CStructDef (CStruct _ fields _ _)) -> do
            -- We only have a struct constructor, since struct projectors are replaced by the `parse` statement
            let fieldTys = map snd fields
            let rty = FStruct tname fields
            funcs %= M.insert tname (fieldTys, rty)
    setupEnv tydefs


