{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module PrettyRust where
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Trans
import Prettyprinter
import Data.Map.Strict as M
import Rust


instance Pretty BorrowKind where
    pretty RMut = pretty "&mut "
    pretty RShared = pretty "&"


instance Pretty RustTy where
    pretty (RTRef bk ty) = pretty bk <> pretty ty
    pretty (RTVec ty) = pretty "Vec" <> angles (pretty ty)
    pretty (RTSlice ty) = pretty "[" <> pretty ty <> pretty "]"
    pretty (RTArray ty n) = pretty "[" <> pretty ty <> pretty ";" <+> pretty n <> pretty "]"
    pretty (RTTuple tys) = pretty "(" <> hsep (punctuate comma (fmap pretty tys)) <> pretty ")"
    pretty (RTOption ty) = pretty "Option" <> angles (pretty ty)
    pretty (RTNamed name) = pretty name
    pretty RTUnit = pretty "()"
    pretty RTBool = pretty "bool"
    pretty RTU8 = pretty "u8"
    pretty RTUsize = pretty "usize"

prettyTyAnnot :: Maybe RustTy -> Doc ann
prettyTyAnnot Nothing = pretty ""
prettyTyAnnot (Just ty) = colon <+> pretty ty

instance Pretty RustExpr where
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
    pretty (RCall (name, args)) = pretty name <> parens (hsep (punctuate comma (fmap pretty args)))
    pretty (RVar name) = pretty name
    pretty (RBorrow (bk, expr)) = pretty bk <> pretty expr
    pretty (RDeref expr) = pretty "*" <> pretty expr
    pretty RUnit = pretty "()"
    pretty (RUsizeLit n) = pretty n <> pretty "usize"

instance Pretty RustFunc where
    pretty (RustFunc name args retTy body) = 
        pretty "fn" <+> pretty name <> 
        parens (hsep (punctuate comma (fmap (\(n, ty) -> pretty n <> colon <+> pretty ty) args)))
        <+> pretty "->" <+> pretty retTy <+> pretty "{" <> line <>
            indent 4 (pretty body) <> line <>
        pretty "}"

instance Pretty RustTyDecl where
    pretty (RustTyDecl (name, ty)) = pretty "type" <+> pretty name <+> pretty "=" <+> pretty ty <> semi

instance Pretty RustTraitImpl where
    pretty (RustTraitImpl traitName forTy traitTys traitFuncs) = 
        pretty "impl" <+> pretty traitName <+> pretty "for" <+> pretty forTy <+> pretty "{" <> line <>
            indent 4 (vsep (fmap pretty traitTys)) <> line <>
            indent 4 (vsep (fmap pretty traitFuncs)) <> line <>
        pretty "}"

instance Pretty RustStructDecl where
    pretty (RustStructDecl name fields implBlock traitImpls) = 
        pretty "pub struct" <+> pretty name <+> pretty "{" <> line <>
            indent 4 (vsep (fmap (\(n, ty) -> pretty n <> colon <+> pretty ty <> comma) fields)) <> line <>
        pretty "}" <> line <> line <>
        pretty "impl" <+> pretty name <+> pretty "{" <> line <>
            indent 4 (vsep (fmap pretty implBlock)) <> line <>
        pretty "}" <> line <> line <>
        vsep (fmap pretty traitImpls)

instance Pretty RustEnumDecl where
    pretty (RustEnumDecl name variants implBlock traitImpls) = 
        pretty "pub enum" <+> pretty name <+> pretty "{" <> line <>
            indent 4 (vsep (fmap (\(n, ty) -> pretty n <> prettyTyAnnot ty <> comma) variants)) <> line <>
        pretty "}" <> line <> line <>
        pretty "impl" <+> pretty name <+> pretty "{" <> line <>
            indent 4 (vsep (fmap pretty implBlock)) <> line <>
        pretty "}" <> line <> line <>
        vsep (fmap pretty traitImpls)
