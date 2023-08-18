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
import Data.Type.Equality
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Unsafe
import Unbound.Generics.LocallyNameless.TH
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import AST

data CTy =
    CTData
    | CTDataWithLength AExpr
    | CTOption CTy
    | CTConst (Path)
    | CTBool
    -- | CTUnion CTy CTy
    | CTUnit
    | CTName NameExp -- Singleton type
    | CTVK NameExp -- Singleton type
    | CTDH_PK NameExp -- Singleton type
    | CTEnc_PK NameExp -- Singleton type
    | CTSS NameExp NameExp -- Singleton type
    deriving (Show, Generic, Typeable)

instance Alpha CTy
instance Subst AExpr CTy

-- For struct compilation, not general
concretifyTy :: Fresh m => Ty -> m CTy
concretifyTy t =
  case t^.val of
    TData _ _ -> return CTData
    TDataWithLength _ l -> return $ CTDataWithLength l
    TRefined t _ -> concretifyTy t
    TOption t -> do
      ct <- concretifyTy t
      return $ CTOption ct
    TCase _ t t' -> do
      ct <- concretifyTy t
      ct' <- concretifyTy t'
      case (ct, ct') of
        (cct, CTData) -> return cct
        (CTData, cct') -> return cct'
        _ -> if ct `aeq` ct' then return ct else error "concretifyTy on TCase failed"
    TConst s _ -> return $ CTConst s
    TBool _ -> return CTBool
    TUnion t t' -> do
      ct <- concretifyTy t
      ct' <- concretifyTy t'
      case (ct, ct') of
        (cct, CTData) -> return cct
        (CTData, cct') -> return cct'
        _ -> if ct `aeq` ct' then return ct else error "concretifyTy on TUnion failed"
      -- return $ CTUnion ct ct'
    TUnit -> return CTUnit
    TName n -> return $ CTName n
    TVK n -> return $ CTVK n
    TDH_PK n -> return $ CTDH_PK n
    TEnc_PK n -> return $ CTEnc_PK n
    TSS n n' -> return $ CTSS n n'
    TAdmit -> error "concretifyTy on TAdmit"
    TExistsIdx it -> do
      (_, t) <- unbind it
      concretifyTy t

doConcretifyTy :: Ty -> CTy
doConcretifyTy = runFreshM . concretifyTy

data CExpr =
    CSkip
    | CInput (Bind (DataVar, EndpointVar) CExpr)
    | COutput AExpr (Maybe Endpoint)
    | CLet CExpr (Bind DataVar CExpr)
    | CIf AExpr CExpr CExpr
    | CRet AExpr
    | CCall Path ([Idx], [Idx]) [AExpr]
    | CCase AExpr [(String, Either CExpr (Bind DataVar CExpr))]
    | CTLookup Path AExpr
    | CTWrite Path AExpr AExpr
    | CCrypt CryptOp [AExpr]
    deriving (Show, Generic, Typeable)

instance Alpha CExpr
instance Subst AExpr CExpr

concretify :: Fresh m => Expr -> m CExpr
concretify e =
    case e^.val of
      EInput xse -> do
          let (xe, e) = unsafeUnbind xse
          c <- concretify e
          return $ CInput $ bind xe c
      EOutput a eo -> return $ COutput a eo
      ELet e1 _ _ _ xk -> do
          e1' <- concretify e1
          let (x, k) = unsafeUnbind xk
          k' <- concretify k
          return $ CLet e1' (bind x k')
      EUnionCase a xk -> do
          (x, k) <- unbind xk
          k' <- concretify k
          return $ subst x a k'
      EUnpack a ixk -> do
          ((i, x), k) <- unbind ixk
          k' <- concretify k
          return $ subst x a k' -- i is dangling here, but that shouldn't matter
      EChooseIdx _ ixk -> do
          (i, k) <- unbind ixk
          k' <- concretify k
          return k' -- i is free here; irrelevant
      EIf a e1 e2 -> do
          c1 <- concretify e1
          c2 <- concretify e2
          return $ CIf a c1 c2
      ERet a -> return $ CRet a
      EDebug _ -> return $ CSkip 
      EAssert _ -> return $ CSkip
      EAssume _ -> error "Concretify on assume"
      EAdmit -> error "Concretify on admit"
      ECall a b c -> return $ CCall a b c
      ECase a cases -> do
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
          return $ CLet a' (bind avar $ (CCase (mkSpanned $ AEVar (ignore $ show avar) avar) cases'))
      EPCase _ _ k -> concretify k
      EFalseElim e -> concretify e
      ETLookup n a -> return $ CTLookup n a
      ETWrite n a a2 -> return $ CTWrite n a a2
      ECrypt op args -> return $ CCrypt op args
      e -> error $ "TODO: unimplemented case for concretify: " ++ show e

doConcretify :: Expr -> CExpr
doConcretify = runFreshM . concretify

instance Pretty CTy where
    pretty CTData = pretty "Data"
    pretty CTUnit =
        pretty "unit"
    pretty CTBool =
            pretty "Bool"
    pretty (CTDataWithLength a) =
            pretty "Data " <+> pretty "|" <> pretty a <> pretty "|"
    pretty (CTOption t) =
            pretty "Option" <> pretty t
    pretty (CTConst n) =
            pretty n
    pretty (CTName n) =
            pretty "Name(" <> pretty n <> pretty ")"
    pretty (CTVK n) =
            pretty "vk(" <> pretty n <> pretty ")"
    pretty (CTDH_PK n) =
            pretty "dhpk(" <> pretty n <> pretty ")"
    pretty (CTEnc_PK n) =
            pretty "encpk(" <> pretty n <> pretty ")"
    pretty (CTSS n m) =
            pretty "shared_secret(" <> pretty n <> pretty ", " <> pretty m <> pretty ")"
    -- pretty (CTUnion t1 t2) =
    --     pretty "Union<" <> pretty t1 <> pretty "," <> pretty t2 <> pretty ">"

instance Pretty CExpr where
    pretty CSkip = pretty "skip"
    pretty (CInput xsk) = 
        let (x, sk) = prettyBind xsk in
        pretty "input" <+> x <> comma <+> sk
    pretty (COutput a l) = pretty "output " <> pretty a <+> (case l of
       Nothing -> pretty ""
       Just s -> pretty "to" <+> pretty s)
    pretty (CLet e xk) =
        let (x, k) = prettyBind xk in
        pretty "let" <+> x <+> pretty "=" <+> pretty e <+> pretty "in" <> line <> k
    pretty (CIf a e1 e2) =
        pretty "if" <+> pretty a <+> pretty "then" <+> pretty e1 <+> pretty "else" <+> pretty e2
    pretty (CRet a) = pretty "ret " <> pretty a
    pretty (CCall f is as) = 
        let inds = case is of
                     ([], []) -> mempty
                     (v1, v2) -> pretty "<" <> mconcat (map pretty v1) <> pretty "@" <> mconcat (map pretty v2) <> pretty ">"
        in
        pretty f <> inds <> tupled (map pretty as)
    pretty (CCase a xs) =
        let pcases =
                map (\(c, o) ->
                    case o of
                      Left e -> pretty "|" <+> pretty c <+> pretty "=>" <+> pretty e
                      Right xe -> let (x, e) = prettyBind xe in pretty "|" <+> pretty c <+> x <+> pretty "=>" <+> e
                    ) xs in
        pretty "case" <+> pretty a <> line <> vsep pcases
    pretty (CTLookup n a) = pretty "lookup" <> tupled [pretty a]
    pretty (CTWrite n a a') = pretty "write" <> tupled [pretty a, pretty a']
    pretty (CCrypt cop as) = pretty cop <> tupled (map pretty as)

