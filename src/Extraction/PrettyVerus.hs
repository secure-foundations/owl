{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module PrettyVerus where
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Trans
import Prettyprinter
import Data.Map.Strict as M
import Verus


instance Pretty BorrowKind where
    pretty RMut = pretty "&mut "
    pretty RShared = pretty "&"

instance Pretty Lifetime where
    pretty lt = pretty "'" <> pretty lt

-- instance Pretty VerusName where
--     pretty (VN name Nothing) = pretty name
--     pretty (VN name (Just lt)) = pretty name <> angles (pretty lt)

-- prettyLtOf :: VerusName -> Doc ann
-- prettyLtOf (VN _ Nothing) = pretty ""
-- prettyLtOf (VN _ (Just lt)) = angles (pretty lt)

prettyLtOfT :: VerusTy -> Doc ann
prettyLtOfT (RTWithLifetime _ lt) = angles (pretty lt)
prettyLtOfT (RTOwlBuf lt) = angles (pretty lt)
prettyLtOfT _ = pretty ""

instance Pretty ConstUsize where
    pretty (CUsizeLit n) = pretty n
    pretty (CUsizeConst n) = pretty n
    pretty (CUsizePlus a b) = pretty a <+> pretty "+" <+> pretty b

instance Pretty VerusTy where
    pretty (RTRef bk ty) = pretty bk <> pretty ty
    pretty (RTVec ty) = pretty "Vec" <> angles (pretty ty)
    pretty (RTSlice ty) = pretty "[" <> pretty ty <> pretty "]"
    pretty (RTArray ty n) = pretty "[" <> pretty ty <> pretty ";" <+> pretty n <> pretty "]"
    pretty (RTTuple tys) = pretty "(" <> hsep (punctuate comma (fmap pretty tys)) <> pretty ")"
    pretty (RTOption ty) = pretty "Option" <> angles (pretty ty)
    pretty (RTParam ty targs) = pretty ty <> angles (hsep (punctuate comma (fmap pretty targs)))
    pretty (RTNamed name) = pretty name
    pretty (RTWithLifetime ty lt) = pretty ty <> angles (pretty lt)
    pretty (RTOwlBuf lt) = pretty "OwlBuf" <> angles (pretty lt)
    pretty RTUnit = pretty "()"
    pretty RTBool = pretty "bool"
    pretty RTU8 = pretty "u8"
    pretty RTUsize = pretty "usize"
    pretty RTVerusGhost = pretty "Ghost<()>"

prettyTyAnnot :: Maybe VerusTy -> Doc ann
prettyTyAnnot Nothing = pretty ""
prettyTyAnnot (Just ty) = colon <+> pretty ty

instance Pretty VerusExpr where
    -- Special case for `let _ = ...;` where we omit the `let _ =`
    pretty (RLet (False, "_", Nothing, expr) rest) = 
        pretty expr <> semi <> line <> pretty rest
    pretty (RLet (lt, name, ty, expr) rest) = 
        pretty "let" <+> pretty (if lt then "mut " else "") <> pretty name <> prettyTyAnnot ty
        <+> pretty "=" <+> pretty expr <> semi <> line <> pretty rest
    pretty (RIfThenElse cond thenBranch elseBranch) =
        pretty "if" <+> pretty cond <+> pretty "{" <> line <> 
            pretty thenBranch <> line <> 
        pretty "}" <+> pretty "else" <+> pretty "{" <> line <>
            pretty elseBranch <> line <>
        pretty "}"
    pretty (RAssign name expr) = pretty name <+> pretty "=" <+> pretty expr <> semi <> line
    pretty (RCall name args) = pretty name <> parens (hsep (punctuate comma (fmap pretty args)))
    pretty (RDotCall name func args) = pretty name <> pretty "." <> pretty func <> parens (hsep (punctuate comma (fmap pretty args)))
    pretty (RFieldSel name field) = pretty name <> pretty "." <> pretty field
    pretty (RVar name) = pretty name
    pretty (RBorrow bk expr) = pretty bk <> pretty expr
    pretty (RDeref expr) = pretty "*" <> pretty expr
    pretty (RInfixOp lhs op rhs) = pretty lhs <+> pretty op <+> pretty rhs
    pretty RUnit = pretty "()"
    pretty (RUsizeLit n) = pretty n <> pretty "usize"
    pretty (RBoolLit b) = if b then pretty "true" else pretty "false"
    pretty (RStructLit name fields) = pretty name <+> pretty "{" <> line <>
            indent 4 (vsep (fmap (\(n, e) -> pretty n <+> pretty ":" <+> pretty e <> comma) fields)) <> line <>
        pretty "}"

instance Pretty VerusSpecExpr where
    pretty (VSIfThenElse cond thenBranch elseBranch) =
        pretty "if" <+> pretty cond <+> pretty "{" <> line <> 
            pretty thenBranch <> line <> 
        pretty "}" <+> pretty "else" <+> pretty "{" <> line <>
            pretty elseBranch <> line <>
        pretty "}"
    pretty (VSCall name args) = pretty name <> parens (hsep (punctuate comma (fmap pretty args)))
    pretty (VSDotCall name func args) = pretty name <> pretty "." <> pretty func <> parens (hsep (punctuate comma (fmap pretty args)))
    pretty (VSFieldSel name field) = pretty name <> pretty "." <> pretty field
    pretty (VSVar name) = pretty name
    pretty (VSDeref expr) = pretty "*" <> pretty expr
    pretty (VSInfixOp lhs op rhs) = pretty lhs <+> pretty op <+> pretty rhs
    pretty VSUnit = pretty "()"
    pretty (VSUsizeLit n) = pretty n <> pretty "usize"
    pretty (VSBoolLit b) = if b then pretty "true" else pretty "false"
    pretty (VSSpecImplies lhs rhs) = pretty lhs <+> pretty "==>" <+> pretty rhs
    pretty (VSSpecMatches lhs rhs) = pretty lhs <+> pretty "matches" <+> pretty rhs
    pretty (VSSpecArrow lhs rhs) = pretty lhs <> pretty "->" <> pretty rhs


instance Pretty VerusFuncMode where
    pretty VOpenSpec = pretty "open spec"
    pretty VClosedSpec = pretty "closed spec"
    pretty VProof = pretty "proof"
    pretty VExec = pretty "exec"

instance Pretty VerusArg where
    pretty (SelfArg bk) = pretty bk <> pretty "self" 
    pretty (Arg name ty) = pretty name <> colon <+> pretty ty

instance Pretty VerusFunc where
    pretty (VerusFunc name mode externalBody verifierOpaque args retTy req ens body) = 
        (if externalBody then pretty "#[verifier(external_body)]" <> line else pretty "") <>
        (if verifierOpaque then pretty "#[verifier::opaque]" <> line else pretty "") <>
        pretty "pub" <+> pretty mode <+> pretty "fn" <+> pretty name <> 
        parens (hsep (punctuate comma (fmap pretty args)))
        <+> pretty "->" <+> pretty retTy <> line <> 
            if Data.List.null req then pretty "" else indent 4 (pretty "requires" <> line <> indent 4 (vsep . punctuate comma $ fmap pretty req) <> comma) <> line <>
            if Data.List.null ens then pretty "" else indent 4 (pretty "ensures"  <> line <> indent 4 (vsep . punctuate comma $ fmap pretty ens) <> comma) <> line <>
        pretty "{" <> line <>
            indent 4 (pretty body) <> line <>
        pretty "}"

instance Pretty VerusTyDecl where
    pretty (VerusTyDecl (name, ty)) = pretty "type" <+> pretty name <+> pretty "=" <+> pretty ty <> semi

instance Pretty VerusTraitImpl where
    pretty (VerusTraitImpl traitName forTy traitTys traitFuncs) = 
        pretty "impl" <> prettyLtOfT forTy <+> pretty traitName <+> pretty "for" <+> pretty forTy <+> pretty "{" <> line <>
            indent 4 (vsep (fmap pretty traitTys)) <> line <>
            indent 4 (vsep (fmap pretty traitFuncs)) <> line <>
        pretty "}"

-- instance Pretty VerusStructDecl where
--     pretty (VerusStructDecl name fields implBlock traitImpls) = 
--         pretty "pub struct" <+> pretty name <+> pretty "{" <> line <>
--             indent 4 (vsep (fmap (\(n, ty) -> pretty n <> colon <+> pretty ty <> comma) fields)) <> line <>
--         pretty "}" <> line <> line <>
--         pretty "impl" <> prettyLtOf name <+> pretty name <+> pretty "{" <> line <>
--             indent 4 (vsep (fmap pretty implBlock)) <> line <>
--         pretty "}" <> line <> line <>
--         vsep (fmap pretty traitImpls)

-- instance Pretty VerusEnumDecl where
--     pretty (VerusEnumDecl name variants implBlock traitImpls) = 
--         pretty "pub enum" <+> pretty name <+> pretty "{" <> line <>
--             indent 4 (vsep (fmap (\(n, ty) -> pretty n <> prettyTyAnnot ty <> comma) variants)) <> line <>
--         pretty "}" <> line <> line <>
--         pretty "impl" <> prettyLtOf name <+> pretty name <+> pretty "{" <> line <>
--             indent 4 (vsep (fmap pretty implBlock)) <> line <>
--         pretty "}" <> line <> line <>
--         vsep (fmap pretty traitImpls)
