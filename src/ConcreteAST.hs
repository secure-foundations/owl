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
    | CTVar TyName
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
    TVar s _ -> return $ CTVar s
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
    | CSamp DistrName [AExpr]
    | CIf AExpr CExpr CExpr
    | CRet AExpr
    | CCall String ([Idx], [Idx]) [AExpr]
    | CCase AExpr [(String, Either CExpr (Bind DataVar CExpr))]
    | CTLookup String AExpr
    | CTWrite String AExpr AExpr
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
      ELet e1 _ _ xk -> do
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
      ESamp x y -> return $ CSamp x y
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
          cases' <- forM cases $ \(c, o) ->
              case o of
                Left e -> do
                    e' <- concretify e
                    return (c, Left e')
                Right (_, xk) -> do
                    let (x, k) = unsafeUnbind xk
                    k' <- concretify k
                    return (c, Right $ bind x k')
          return $ CCase a cases'
      ECorrCase _ k -> concretify k
      EFalseElim e -> concretify e
      ETLookup n a -> return $ CTLookup n a
      ETWrite n a a2 -> return $ CTWrite n a a2

-- doConcretify :: Expr -> CExpr
-- doConcretify = runFreshM . concretify


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
    pretty (CTVar n) =
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


-- NB: This is a trusted component of the extraction pipeline!
-- The pretty-printer for CExprs is used to print out the Verus spec code 
-- (in the form that is parsed by macro into an ITree datatype in Verus)

-- Some helper functions:
coinsSize :: DistrName -> Doc ann
coinsSize "enc" = pretty "TAG_SIZE"

prettyEndpoint :: Endpoint -> Doc ann
prettyEndpoint (Endpoint evar) = pretty evar
prettyEndpoint (EndpointLocality (Locality s _)) = pretty "Endpoint::Loc_" <> pretty s

replacePrimes :: String -> String
replacePrimes = map (\c -> if c == '\'' || c == '.' then '_' else c)

replacePrimes' :: Doc ann -> Doc ann
replacePrimes' = pretty . replacePrimes . show

rustifyName :: String -> String
rustifyName s = "owl_" ++ replacePrimes s

rustifyName' :: Doc ann -> Doc ann
rustifyName' = pretty . rustifyName . show

locName :: String -> String
locName x = "loc_" ++ replacePrimes x

sidName :: String -> String
sidName x = "sid_" ++ replacePrimes x

specName :: String -> String
specName s = "owlSpec_" ++ replacePrimes s


specPrettyAE :: AExpr -> Doc ann
specPrettyAE ae = specPrettyAE' (ae ^. val) where
    specPrettyAE' (AEVar s n) = pretty (unignore s)
    specPrettyAE' (AEApp f _ as) = pretty f <> tupled (map specPrettyAE as)
    specPrettyAE' (AEString s) = pretty "\"" <> pretty s <> pretty "\""
    specPrettyAE' (AELenConst s) = pretty s <> pretty "_len"
    specPrettyAE' (AEInt i) = pretty i
    specPrettyAE' (AEGet ne) = pretty "Some" <> parens (parens (pretty "*loc." <> rustifyName' (pretty ne)) <> pretty ".view()")
    specPrettyAE' (AEGetEncPK ne) = pretty "get_encpk" <> pretty "(" <> pretty ne <> pretty ")"
    specPrettyAE' (AEGetVK ne) = pretty "get_vk" <> pretty "(" <> pretty ne <> pretty ")"
    specPrettyAE' (AEPackIdx s a) = specPrettyAE a

instance Pretty CExpr where
    pretty CSkip = pretty "skip"
    pretty (CInput xsk) =
        let (x, sk) = prettyBind xsk in
        parens (pretty "input" <+> x) <+> pretty "in" <> line <> sk
    pretty (COutput a l) = parens $ pretty "output " <> parens (specPrettyAE a) <+> (case l of
       Nothing -> pretty ""
       Just s -> pretty "to" <+> parens (prettyEndpoint s))
    -- Special case for `let _ = samp _ in ...` which is special-cased in the ITree syntax
    pretty (CLet (CSamp d xs) xk) =
        let (x, k) = prettyBind xk in
        parens (pretty "sample" <> parens (coinsSize d <> comma <+> pretty d <> tupled (map specPrettyAE xs) <> comma <+> x)) <+>
        pretty "in" <> line <> k
    pretty (CLet (COutput a l) xk) =
        let (x, k) = prettyBind xk in
        pretty (COutput a l) <+> pretty "in" <> line <> k
    pretty (CLet e xk) =
        let (x, k) = prettyBind xk in
        pretty "let" <+> x <+> pretty "=" <+> pretty e <+> pretty "in" <> line <> k
    pretty (CSamp d xs) = pretty "sample" <> parens (coinsSize d <> comma <+> pretty d <> tupled (map specPrettyAE xs))
    pretty (CIf a e1 e2) = parens $
        pretty "if" <+> parens (specPrettyAE a) <+> pretty "then" <+> parens (pretty e1) <+> pretty "else" <+> parens (pretty e2)
    pretty (CRet a) = parens $ pretty "ret " <> parens (specPrettyAE a)
    pretty (CCall f is as) =
        let inds = case is of
                     ([], []) -> mempty
                     (v1, v2) -> pretty "<" <> mconcat (map pretty v1) <> pretty "@" <> mconcat (map pretty v2) <> pretty ">"
        in
        pretty f <> inds <> tupled (map specPrettyAE as)
    pretty (CCase a xs) =
        let pcases =
                map (\(c, o) ->
                    case o of
                      Left e -> pretty c <+> pretty "=>" <+> braces (pretty e) <> comma
                      Right xe -> let (x, e) = prettyBind xe in pretty c <+> parens x <+> pretty "=>" <+> braces e <> comma
                    ) xs in
        parens $ pretty "case" <+> parens (specPrettyAE a) <> line <> braces (vsep pcases)
    pretty (CTLookup n a) = pretty "lookup" <> tupled [specPrettyAE a]
    pretty (CTWrite n a a') = pretty "write" <> tupled [specPrettyAE a, specPrettyAE a']

