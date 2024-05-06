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
      TConst _ _ -> throwError $ TypeError "invalid constant type in concretifyTy"
      TBool _ -> return $ FBool
      TUnit -> return $ FUnit
      TName ne -> formatTyOfNameExp ne
      TVK ne -> error "unimp"
      TEnc_PK ne -> error "unimp"
      TDH_PK ne -> error "unimp"
      TSS ne1 ne2 -> return $ groupFormatTy
      TAdmit -> throwError $ ErrSomethingFailed "Got admit type during concretization"
      TExistsIdx _ it -> do
          (i, t) <- unbind it
          concretifyTy t -- TODO keep track of indices?
      THexConst s -> return $ hexConstType s

hexConstType :: String -> FormatTy
hexConstType s = FBuf $ Just $ FLConst $ length s `div` 2

groupFormatTy :: FormatTy
groupFormatTy = FBuf $ Just $ FLNamed "group" -- maybe we want internal repr here? 

unifyFormatTy :: FormatTy -> FormatTy -> EM FormatTy
unifyFormatTy t1 t2 =
    case (t1, t2) of
      _ | t1 `aeq` t2 -> return t1
      (FBuf Nothing, _) -> return $ FBuf Nothing
      (_, FBuf Nothing) -> return $ FBuf Nothing
      _ -> throwError $ ErrSomethingFailed $ "Could not unify format types " ++ (show $ owlpretty t1) ++ " and " ++ show (owlpretty t2)

formatTyOfNameExp :: NameExp -> EM FormatTy
formatTyOfNameExp ne = do
    nt <- liftCheck $ TB.getNameType ne
    fl <- fLenOfNameTy nt
    return $ FBuf $ Just fl

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
flenOfFormatTy (FBuf o) = o
flenOfFormatTy (FUnit) = Just $ FLConst 0
flenOfFormatTy FGhost = Just $ FLConst 0
flenOfFormatTy FInt = Just $ FLConst 32 -- todo?
flenOfFormatTy _ = Nothing

concreteTyOfApp :: Path -> [FuncParam] -> [FormatTy] -> EM FormatTy
concreteTyOfApp (PRes pth) =
    case pth of
      PDot PTop "unit" -> \_ _ -> return FUnit
      PDot PTop "true" -> \_ _ -> return FBool
      PDot PTop "false" -> \_ _ -> return FBool
      PDot PTop "eq" -> \_ [x, y] -> do
            unifyFormatTy x y
            return FBool
      PDot PTop "Some" -> \_ [x] -> return $ FOption x
      PDot PTop "None" -> \params [] -> do
            case params of
                [ParamTy owlT] -> do
                    t <- concretifyTy owlT
                    return $ FOption t
                _ -> throwError $ TypeError "Can't infer type of None"
      PDot PTop "andb" -> \_ [x, y] -> return FBool
      PDot PTop "andp" -> \_ [x, y] -> return FUnit
      PDot PTop "notb" -> \_ [x, y] -> return FBool
      PDot PTop "length" -> \_ [x] -> return FInt
      PDot PTop "plus" -> \_ [x, y] -> return FInt
      PDot PTop "crh" -> \_ [x] -> return $ FBuf $ Just $ FLNamed "crh"
      PDot PTop "mult" -> \_ [x, y] -> return FInt
      PDot PTop "zero" -> \_ [] -> return FInt
      PDot PTop "is_group_elem" -> \_ [x] -> return FBool
      PDot PTop "concat" -> \_ [x, y] -> do
          case (flenOfFormatTy x, flenOfFormatTy y) of
            (Nothing, _) -> return $ FBuf Nothing
            (_, Nothing) -> return $ FBuf Nothing
            (Just x, Just y) -> return $ FBuf $ Just $ FLPlus x y
      PDot PTop "xor" -> \_ [x, y] -> do
          t <- unifyFormatTy x y
          case t of
            FBuf (Just _) -> return t
            _ -> throwError $ ErrSomethingFailed $ "cannot extract xor"
      PDot PTop "cipherlen" -> \_ [x] -> return FInt
      PDot PTop "pk_cipherlen" -> \_ [x] -> error "unimp"
      PDot PTop "vk" -> \_ [x] -> return $ FBuf $ Just $ FLNamed "vk"
      PDot PTop "dhpk" -> \_ [x] -> return groupFormatTy
      PDot PTop "enc_pk" -> \_ [x] -> return $ FBuf $ Just $ FLNamed "enc_pk"
      PDot PTop "dh_combine" -> \_ [x, y] -> do
          when (not $ (aeq x groupFormatTy) && (aeq y groupFormatTy)) $
              throwError $ ErrSomethingFailed $ "Cannot extract dh_combine"
          return groupFormatTy
      PDot PTop "checknonce" -> \_ [x, y] -> error "unimp"
      PDot PTop p -> \_ args -> do
        fs <- use funcs
        case fs M.!? p of
            Just (argTys, retTy) -> do
                when (length argTys /= length args) $ throwError $ TypeError $ "Wrong number of arguments to function " ++ p
                forM_ (zip argTys args) $ \(t, a) -> do
                    unifyFormatTy t a
                return retTy
            Nothing -> throwError $ UndefinedSymbol $ show . owlpretty $ p
      _ -> \_ _ -> do
        throwError $ ErrSomethingFailed "Got bad path in concreteTyOfApp"
concreteTyOfApp _ = \_ _ -> do
    throwError $ ErrSomethingFailed "Got bad path in concreteTyOfApp"

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
          encPKFormatTy <- concretifyTy $ mkSpanned $ TEnc_PK n
          s <- concretifyNameExpLoc n
          return $ Typed encPKFormatTy $ CAGetEncPK s
      AEGetVK n -> do
          vkFormatTy <- concretifyTy $ mkSpanned $ TVK n
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


-- TODO: insert call to marshaling based on type analysis 
-- (when data type used as input to crypto op, output, etc)

concretifyExpr :: Expr -> EM (CExpr FormatTy)
concretifyExpr e =
    case e^.val of
      EInput _ xk -> do
          ((x, ep), k) <- unbind xk
          k' <- withVars [(castName x, FBuf Nothing)] $ concretifyExpr k
          return $ Typed (_tty k') $ CInput (FBuf Nothing) $ bind (castName x, ep) k'
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
      EParse a t_target otherwiseCase xsk -> do
            a' <- concretifyAExpr a
            t_target' <- concretifyTy t_target
            otw' <- traverse concretifyExpr otherwiseCase
            (xs, k) <- unbind xsk
            let xs' = map (\(x, s) -> (castName x, s)) xs
            (xtys, xtys') <- case t_target' of
                        FStruct _ fields -> return (zip (map fst xs') (map snd fields), zipWith (curry (\((a,b),c) -> (a,b,c))) xs' (map snd fields))
                        FEnum _ _ -> do
                            when (length xs' /= 1) $ throwError $ TypeError "Expected exactly one argument to EParse for enum"
                            return ([(head xs' ^. _1, t_target')], [(head xs' ^. _1, head xs' ^. _2, t_target')])
                        _ -> throwError $ TypeError $ "Expected datatype as target of EParse, got " ++ (show . owlpretty) t_target'
            pkind <- case a' ^. tty of
                        FBuf _ -> return PFromBuf
                        FStruct _ _ -> return PFromDatatype
                        FEnum _ _ -> return PFromDatatype
                        _ -> throwError $ TypeError $ "Expected buffer or datatype in EParse, got " ++ (show . owlpretty) (a' ^. tty)
            k' <- withVars xtys $ concretifyExpr k
            return $ Typed (k' ^. tty) $ CParse pkind a' t_target' otw' $ bind xtys' k'
      ECase e otherwiseCase xsk -> do
            e' <- concretifyExpr e
            casevalT <- case otherwiseCase of
                Just (t, e) -> concretifyTy t
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
                        k' <- concretifyExpr k
                        return (c, Left k')
                    Right (_, xtk) -> do
                        (x, k) <- unbind xtk
                        let x' = castName x
                        caseTy <- caseTyOf c
                        k' <- withVars [(x', caseTy)] $ concretifyExpr k
                        return (c, Right $ bind x' (caseTy, k'))
            avar <- fresh $ s2n "caseval"
            -- Assume the typechecker already checked that all branches return compatible types,
            -- so we just look at the first one to determine the return type
            retTy <- case head cases' of
                (_, Left k) -> return $ k ^. tty
                (_, Right xtk) -> do
                    let (_, (_, k)) = unsafeUnbind xtk
                    return $ k ^. tty
            let caseStmt = Typed retTy $ CCase (Typed casevalT $ CAVar (ignore "caseval") avar) cases'
            (avar', parseAndCase) <- case otherwiseCase of
                Just (t, otw) -> do
                    let startT = e' ^. tty
                    otw' <- concretifyExpr otw
                    avar' <- fresh $ s2n "parseval"
                    -- We are parsing as part of the case, so we need PFromBuf
                    let p = Typed retTy $
                            CParse PFromBuf (Typed startT $ CAVar (ignore "parseval") avar') casevalT (Just otw') $
                                bind [(avar', ignore "caseval", casevalT)] caseStmt
                    return (avar', p)
                Nothing -> return (avar, caseStmt)
            return $ Typed retTy $ CLet e' Nothing $ bind avar' parseAndCase
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
      ESetOption _ _ e -> concretifyExpr e


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
concretifyCryptOp (CKDF _ _ _ _) cs = throwError $ ErrSomethingFailed "TODO: concretifyCryptOp CKDF"
concretifyCryptOp (CLemma _) cs = throwError $ ErrSomethingFailed "TODO: concretifyCryptOp CLemma"
concretifyCryptOp CAEnc [k, x] = do
    let t = case x ^. tty of
              FBuf (Just fl) -> FBuf $ Just $ FLCipherlen fl
              _ -> FBuf Nothing
    coinsName <- fresh $ s2n "coins"
    let sampFLen = FLNamed "nonce"
    let coinsVar = Typed (FBuf $ Just sampFLen) $ CAVar (ignore "coins") coinsName
    let doEnc = Typed t $ CRet $ Typed t $ CAApp "enc" [k, x, coinsVar]
    return $ Typed t $ CSample sampFLen $ bind coinsName doEnc
concretifyCryptOp CADec [k, c] = do
    let t = FOption $ FBuf Nothing
    return $ Typed t $ CRet $ Typed t $ CAApp "dec" [k, c]
concretifyCryptOp (CEncStAEAD _ _ _) cs = throwError $ ErrSomethingFailed "TODO: concretifyCryptOp CEncStAEAD"
concretifyCryptOp CDecStAEAD cs = throwError $ ErrSomethingFailed "TODO: concretifyCryptOp CDecStAEAD"
concretifyCryptOp CPKEnc cs = throwError $ ErrSomethingFailed "TODO: concretifyCryptOp CPKEnc"
concretifyCryptOp CPKDec cs = throwError $ ErrSomethingFailed "TODO: concretifyCryptOp CPKDec"
concretifyCryptOp CMac cs = throwError $ ErrSomethingFailed "TODO: concretifyCryptOp CMac"
concretifyCryptOp CMacVrfy cs = throwError $ ErrSomethingFailed "TODO: concretifyCryptOp CMacVrfy"
concretifyCryptOp CSign cs = throwError $ ErrSomethingFailed "TODO: concretifyCryptOp CSign"
concretifyCryptOp CSigVrfy cs = throwError $ ErrSomethingFailed "TODO: concretifyCryptOp CSigVrfy"
concretifyCryptOp cop cargs = throwError $ TypeError $
    "Got bad crypt op during concretization: " ++ show (owlpretty cop) ++ ", args " ++ show (owlpretty cargs)



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
        -- cretT <- concretifyTy retT
        case oexpr of
          Nothing -> return Nothing
          Just e -> do
              ce <- concretifyExpr e
              let cretT = ce ^. tty
              --   debugPrint . show . owlpretty $ defName
              --   debugPrint . show . owlpretty $ ce
              return $ Just (cretT, ce)
    case ores of
      Nothing -> return Nothing
      Just res -> return $ Just $ CDef defName res


concretifyTyDef :: String -> TB.TyDef -> EM (Maybe (CTyDef FormatTy))
concretifyTyDef tname (TB.TyAbstract) = return Nothing
concretifyTyDef tname (TB.TyAbbrev t) = return Nothing -- TODO: need to keep track of aliases
concretifyTyDef tname (TB.EnumDef bnd) = do
    (_, ts) <- unbind bnd
    cs <- forM ts $ \(s, ot) -> do
        cot <- traverse concretifyTy ot
        return (s, cot)
    return $ Just $ CEnumDef (CEnum tname (M.fromList cs))
concretifyTyDef tname (TB.StructDef bnd) = do
    (_, dp) <- unbind bnd
    let go dp = case dp of
                  DPDone _ -> return []
                  DPVar t s xres -> do
                      c <- concretifyTy t
                      (_, k) <- unbind xres
                      ck <- go k
                      return $ (s, c) : ck
    s <- go dp
    return $ Just $ CStructDef (CStruct tname s)


setupEnv :: [(String, TB.TyDef)] -> EM ()
setupEnv [] = return ()
setupEnv ((tname, td):tydefs) = do
    tdef <- concretifyTyDef tname td
    case tdef of
        Nothing -> return ()
        Just (CEnumDef (CEnum _ cases)) -> do
            -- We only have case constructors for each case, since enum projectors are replaced by the `case` statement
            let mkCase (cname, cty) = do
                    let argTys = case cty of
                            Just t -> [t]
                            Nothing -> []
                    let rty = FEnum tname $ M.assocs cases
                    funcs %= M.insert cname (argTys, rty)
            mapM_ mkCase (M.assocs cases)
        Just (CStructDef (CStruct _ fields)) -> do
            -- We only have a struct constructor, since struct projectors are replaced by the `parse` statement
            let fieldTys = map snd fields
            let rty = FStruct tname fields
            funcs %= M.insert tname (fieldTys, rty)
    setupEnv tydefs


