{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
module ConcreteAST where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Control.Monad
import Control.Lens
import Prettyprinter
import Pretty
import Data.Type.Equality
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Unsafe
import Unbound.Generics.LocallyNameless.TH
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import ANFPass (isGhostTyAnn)

import AST

data CTy =
    CTData
    | CTDataWithLength AExpr
    | CTOption CTy
    | CTGhost
    | CTConst (Path)
    | CTBool
    -- | CTUnion CTy CTy
    | CTUnit
    | CTName NameExp -- Singleton type
    | CTVK NameExp -- Singleton type
    | CTDH_PK NameExp -- Singleton type
    | CTEnc_PK NameExp -- Singleton type
    | CTSS NameExp NameExp -- Singleton type
    | CTHex String -- hex constant string
    deriving (Show, Generic, Typeable)

instance Alpha CTy
instance Subst AExpr CTy

compatTys :: CTy -> CTy -> Bool
compatTys (CTName n1) (CTName n2) =
    case (n1 ^. val, n2 ^. val) of
        (KDFName _ _ _ nks1 i1 _, KDFName _ _ _ nks2 i2 _) ->
            (nks1 !! i1) `aeq` (nks2 !! i2)
        _ -> n1 `aeq` n2
compatTys (CTDH_PK _) (CTDH_PK _) = True
compatTys ct1 ct2 = ct1 `aeq` ct2

-- For struct compilation, not general
concretifyTy :: Fresh m => Ty -> m CTy
concretifyTy t =
  case t^.val of
    TData _ _ _ -> return CTData
    TGhost -> return CTGhost
    TDataWithLength _ l -> return $ CTDataWithLength l
    TRefined t _ _ -> concretifyTy t
    TOption t -> do
      ct <- concretifyTy t
      return $ CTOption ct
    TCase _ t t' -> do
      ct <- concretifyTy t
      ct' <- concretifyTy t'
      case (ct, ct') of
        (cct, CTData) -> return cct
        (CTData, cct') -> return cct'
        _ -> if ct `compatTys` ct' then return ct else 
            error $ "concretifyTy on TCase failed: " ++ show (owlpretty ct) ++ ", " ++ show (owlpretty ct')
    TConst s _ -> return $ CTConst s
    TBool _ -> return CTBool
    TUnion t t' -> do
      ct <- concretifyTy t
      ct' <- concretifyTy t'
      case (ct, ct') of
        (cct, CTData) -> return cct
        (CTData, cct') -> return cct'
        _ -> if ct `compatTys` ct' then return ct else error "concretifyTy on TUnion failed"
      -- return $ CTUnion ct ct'
    TUnit -> return CTUnit
    TName n -> return $ CTName n
    TVK n -> return $ CTVK n
    TDH_PK n -> return $ CTDH_PK n
    TEnc_PK n -> return $ CTEnc_PK n
    TSS n n' -> return $ CTSS n n'
    TAdmit -> error "concretifyTy on TAdmit"
    TExistsIdx _ it -> do
      (_, t) <- unbind it
      concretifyTy t
    THexConst a -> return $ CTHex a

doConcretifyTy :: Ty -> CTy
doConcretifyTy = runFreshM . concretifyTy

data CExpr =
    CSkip
    | CInput (Bind (DataVar, EndpointVar) CExpr)
    | COutput AExpr (Maybe Endpoint)
    | CLet CExpr (Maybe AExpr) (Bind DataVar CExpr)
    | CLetGhost (Bind DataVar CExpr)
    | CBlock CExpr -- Boundary for scoping; introduced by { }
    | CIf AExpr CExpr CExpr
    | CRet AExpr
    | CCall Path ([Idx], [Idx]) [AExpr]
    | CParse AExpr CTy (Maybe CExpr) (Bind [(DataVar, Ignore String)] CExpr)
    | CCase AExpr (Maybe (CTy, CExpr)) [(String, Either CExpr (Bind DataVar CExpr))]
    | CTLookup Path AExpr
    | CTWrite Path AExpr AExpr
    | CCrypt CryptOp [AExpr]
    | CGetCtr Path ([Idx], [Idx])
    | CIncCtr Path ([Idx], [Idx])
    deriving (Show, Generic, Typeable)

instance Alpha CExpr
instance Subst AExpr CExpr

concretify :: Fresh m => Expr -> m CExpr
concretify e =
    case e^.val of
        EInput _ xse -> do
            let (xe, e) = unsafeUnbind xse
            c <- concretify e
            return $ CInput $ bind xe c
        EOutput a eo -> return $ COutput a eo
        ELet e1 tyann oanf _ xk | isGhostTyAnn tyann -> do
            let (x, k) = unsafeUnbind xk   
            k' <- concretify k
            return $ CLetGhost (bind x k')
        ELet e1 tyann oanf _ xk -> do
            e1' <- concretify e1
            let (x, k) = unsafeUnbind xk
            k' <- concretify k
            return $ CLet e1' oanf (bind x k')
        EBlock e _ -> do
            c <- concretify e
            return $ CBlock c
        EUnionCase a s xk -> do
            (x, k) <- unbind xk
            k' <- concretify k
            return $ subst x a k'
        EUnpack a _ ixk -> do
            ((i, x), k) <- unbind ixk
            k' <- concretify k
            return $ subst x a k' -- i is dangling here, but that shouldn't matter
        EChooseIdx _ _ ixk -> do
            (i, k) <- unbind ixk
            k' <- concretify k
            return k' -- i is free here; irrelevant
        EIf a e1 e2 -> do
            c1 <- concretify e1
            c2 <- concretify e2
            return $ CIf a c1 c2
        EGuard ae e -> do
            -- The aexpr must have type bool, and the expr must have type Option<_>
            -- During concretization we desugar into an if statement
            c <- concretify e
            -- During typechecking the option needs to carry around its type, but during 
            -- extraction this is not required, so we just leave it blank
            return $ CIf ae c (CRet (mkSpanned (AEApp (topLevelPath "None") [] [])))
        ERet a -> return $ CRet a
        EDebug _ -> return CSkip 
        EAssert _ -> return CSkip
        EAssume _ -> return CSkip -- error "Concretify on assume"
        EAdmit -> error "Concretify on admit"
        EForallBV _ _ -> return CSkip
        EForallIdx _ _ -> return CSkip
        ECall a b c -> return $ CCall a b c
        EParse ae t ok bindpat -> do
            let (pats, k) = unsafeUnbind bindpat
            k' <- concretify k
            ok' <- traverse concretify ok
            t' <- concretifyTy t
            return $ CParse ae t' ok' (bind pats k')
        ECase a otk cases -> do 
            a' <- concretify a
            cases' <- forM cases $ \(c, o) ->
                case o of
                    Left e -> do
                        e' <- concretify e
                        return (c, Left e')
                    Right (_, xk) -> do
                        let (x, k) = unsafeUnbind xk
                        k' <- concretify k
                        return (c, Right $ bind x k')
            avar <- fresh $ s2n "caseval"
            otk' <- case otk of
                Nothing -> return Nothing
                Just (t,k) -> do
                    t' <- concretifyTy t
                    k' <- concretify k
                    return $ Just (t', k')
            return $ CLet a' Nothing (bind avar $ CCase (mkSpanned $ AEVar (ignore $ show avar) avar) otk' cases')
        EPCase _ _ _ k -> concretify k
        EFalseElim e _ -> concretify e
        ETLookup n a -> return $ CTLookup n a
        ETWrite n a a2 -> return $ CTWrite n a a2
        ECrypt (CLemma _) _ -> return CSkip -- lemma calls are ghost
        ECrypt op args -> return $ CCrypt op args
        EIncCtr p idxs -> return $ CIncCtr p idxs
        EGetCtr p idxs -> return $ CGetCtr p idxs
        ESetOption _ _ e -> concretify e
        ELetGhost _ _ xk -> do
            -- TODO check this
            let (x, k) = unsafeUnbind xk
            k' <- concretify k
            return $ CLetGhost (bind x k')
        ECorrCaseNameOf _ _ k -> concretify k
        -- _ -> error $ "Concretify on " ++ show (owlpretty e)

doConcretify :: Expr -> CExpr
doConcretify = runFreshM . concretify

instance OwlPretty CTy where
    owlpretty CTData = owlpretty "Data"
    owlpretty CTUnit =
        owlpretty "unit"
    owlpretty CTBool =
            owlpretty "Bool"
    owlpretty (CTDataWithLength a) =
            owlpretty "Data " <+> owlpretty "|" <> owlpretty a <> owlpretty "|"
    owlpretty (CTOption t) =
            owlpretty "Option" <> owlpretty t
    owlpretty (CTConst n) =
            owlpretty n
    owlpretty (CTName n) =
            owlpretty "Name(" <> owlpretty n <> owlpretty ")"
    owlpretty (CTVK n) =
            owlpretty "vk(" <> owlpretty n <> owlpretty ")"
    owlpretty (CTDH_PK n) =
            owlpretty "dhpk(" <> owlpretty n <> owlpretty ")"
    owlpretty (CTEnc_PK n) =
            owlpretty "encpk(" <> owlpretty n <> owlpretty ")"
    owlpretty (CTSS n m) =
            owlpretty "shared_secret(" <> owlpretty n <> owlpretty ", " <> owlpretty m <> owlpretty ")"
    owlpretty (CTHex a) =
            owlpretty "Const(" <> owlpretty "0x" <> owlpretty a <> owlpretty ")"
    owlpretty CTGhost = 
            owlpretty "Ghost"
    -- owlpretty (CTUnion t1 t2) =
    --     owlpretty "Union<" <> owlpretty t1 <> owlpretty "," <> owlpretty t2 <> owlpretty ">"

instance OwlPretty CExpr where
    owlpretty CSkip = owlpretty "skip"
    owlpretty (CInput xsk) = 
        let (x, sk) = owlprettyBind xsk in
        owlpretty "input" <+> x <> pretty ";" <+> sk
    owlpretty (COutput a l) = owlpretty "output " <> owlpretty a <+> (case l of
       Nothing -> owlpretty ""
       Just s -> owlpretty "to" <+> owlpretty s)
    owlpretty (CLet e oanf xk) =
        let (x, k) = owlprettyBind xk in
        owlpretty "let" <> braces (owlpretty oanf) <+> x <+> owlpretty "=" <+> owlpretty e <+> owlpretty "in" <> line <> k
    owlpretty (CBlock e) = owlpretty "{" <+> owlpretty e <+> owlpretty "}"
    owlpretty (CIf a e1 e2) =
        owlpretty "if" <+> owlpretty a <+> owlpretty "then" <+> owlpretty e1 <+> owlpretty "else" <+> owlpretty e2
    owlpretty (CRet a) = owlpretty "ret " <> owlpretty a
    owlpretty (CCall f is as) = 
        let inds = case is of
                     ([], []) -> mempty
                     (v1, v2) -> owlpretty "<" <> mconcat (map owlpretty v1) <> owlpretty "@" <> mconcat (map owlpretty v2) <> owlpretty ">"
        in
        owlpretty f <> inds <> tupled (map owlpretty as)
    owlpretty (CCase a otk xs) =
        let pcases =
                map (\(c, o) ->
                    case o of
                      Left e -> owlpretty "|" <+> owlpretty c <+> owlpretty "=>" <+> owlpretty e
                      Right xe -> let (x, e) = owlprettyBind xe in owlpretty "|" <+> owlpretty c <+> x <+> owlpretty "=>" <+> e
                    ) xs in
        owlpretty "case" <+> owlpretty a <> line <> vsep pcases
    owlpretty (CTLookup n a) = owlpretty "lookup" <> tupled [owlpretty a]
    owlpretty (CTWrite n a a') = owlpretty "write" <> tupled [owlpretty a, owlpretty a']
    owlpretty (CCrypt cop as) = owlpretty cop <> tupled (map owlpretty as)
    owlpretty (CIncCtr p idxs) = owlpretty "inc_counter" <> angles (owlpretty idxs) <> parens (owlpretty p)
    owlpretty (CGetCtr p idxs) = owlpretty "get_counter" <> angles (owlpretty idxs) <> parens (owlpretty p)
    owlpretty (CParse ae t ok bindpat) = 
        let (pats, k) = owlprettyBind bindpat in
        owlpretty "parse" <+> owlpretty ae <+> owlpretty "as" <+> owlpretty t <> parens pats <+> owlpretty "otherwise" <+> owlpretty ok <+> owlpretty "in" <> line <> k
    owlpretty (CLetGhost xk) =
        let (x, k) = owlprettyBind xk in
        owlpretty "letghost" <+> x <+> owlpretty "in" <> line <> k
