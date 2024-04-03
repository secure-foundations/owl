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
import Pretty (OwlDoc, OwlPretty(..))


instance OwlPretty BorrowKind where
    owlpretty RMut = owlpretty "&mut "
    owlpretty RShared = owlpretty "&"


instance OwlPretty RustTy where
    owlpretty (RTRef bk ty) = owlpretty bk <> owlpretty ty
    owlpretty (RTVec ty) = owlpretty "Vec" <> angles (owlpretty ty)
    owlpretty (RTSlice ty) = owlpretty "[" <> owlpretty ty <> owlpretty "]"
    owlpretty (RTArray ty n) = owlpretty "[" <> owlpretty ty <> owlpretty ";" <+> owlpretty n <> owlpretty "]"
    owlpretty (RTTuple tys) = owlpretty "(" <> hsep (punctuate comma (fmap owlpretty tys)) <> owlpretty ")"
    owlpretty (RTOption ty) = owlpretty "Option" <> angles (owlpretty ty)
    owlpretty (RTNamed name) = owlpretty name
    owlpretty RTUnit = owlpretty "()"
    owlpretty RTBool = owlpretty "bool"
    owlpretty RTU8 = owlpretty "u8"
    owlpretty RTUsize = owlpretty "usize"

owlprettyTyAnnot :: Maybe RustTy -> OwlDoc
owlprettyTyAnnot Nothing = owlpretty ""
owlprettyTyAnnot (Just ty) = colon <+> owlpretty ty

instance OwlPretty RustExpr where
    -- Special case for `let _ = ...;` where we omit the `let _ =`
    owlpretty (RLet (False, "_", Nothing, expr) rest) = 
        owlpretty expr <> semi <> line <> owlpretty rest
    owlpretty (RLet (lt, name, ty, expr) rest) = 
        owlpretty "let" <+> owlpretty (if lt then "mut " else "") <> owlpretty name <> owlprettyTyAnnot ty
        <+> owlpretty "=" <+> owlpretty expr <> semi <> line <> owlpretty rest
    owlpretty (RIfThenElse cond thenBranch elseBranch) =
        owlpretty "if" <+> owlpretty cond <+> owlpretty "{" <> line <> 
            owlpretty thenBranch <> line <> 
        owlpretty "}" <+> owlpretty "else" <+> owlpretty "{" <> line <>
            owlpretty elseBranch <> line <>
        owlpretty "}"
    owlpretty (RAssign name expr) = owlpretty name <+> owlpretty "=" <+> owlpretty expr <> semi <> line
    owlpretty (RCall (name, args)) = owlpretty name <> parens (hsep (punctuate comma (fmap owlpretty args)))
    owlpretty (RVar name) = owlpretty name
    owlpretty (RBorrow (bk, expr)) = owlpretty bk <> owlpretty expr
    owlpretty (RDeref expr) = owlpretty "*" <> owlpretty expr
    owlpretty RUnit = owlpretty "()"
    owlpretty (RUsizeLit n) = owlpretty n <> owlpretty "usize"

instance OwlPretty RustFunc where
    owlpretty (RustFunc name args retTy body) = 
        owlpretty "fn" <+> owlpretty name <> 
        parens (hsep (punctuate comma (fmap (\(n, ty) -> owlpretty n <> colon <+> owlpretty ty) args)))
        <+> owlpretty "->" <+> owlpretty retTy <+> owlpretty "{" <> line <>
            indent 4 (owlpretty body) <> line <>
        owlpretty "}"

instance OwlPretty RustTyDecl where
    owlpretty (RustTyDecl (name, ty)) = owlpretty "type" <+> owlpretty name <+> owlpretty "=" <+> owlpretty ty <> semi

instance OwlPretty RustTraitImpl where
    owlpretty (RustTraitImpl traitName forTy traitTys traitFuncs) = 
        owlpretty "impl" <+> owlpretty traitName <+> owlpretty "for" <+> owlpretty forTy <+> owlpretty "{" <> line <>
            indent 4 (vsep (fmap owlpretty traitTys)) <> line <>
            indent 4 (vsep (fmap owlpretty traitFuncs)) <> line <>
        owlpretty "}"

instance OwlPretty RustStructDecl where
    owlpretty (RustStructDecl name fields implBlock traitImpls) = 
        owlpretty "pub struct" <+> owlpretty name <+> owlpretty "{" <> line <>
            indent 4 (vsep (fmap (\(n, ty) -> owlpretty n <> colon <+> owlpretty ty <> comma) fields)) <> line <>
        owlpretty "}" <> line <> line <>
        owlpretty "impl" <+> owlpretty name <+> owlpretty "{" <> line <>
            indent 4 (vsep (fmap owlpretty implBlock)) <> line <>
        owlpretty "}" <> line <> line <>
        vsep (fmap owlpretty traitImpls)

instance OwlPretty RustEnumDecl where
    owlpretty (RustEnumDecl name variants implBlock traitImpls) = 
        owlpretty "pub enum" <+> owlpretty name <+> owlpretty "{" <> line <>
            indent 4 (vsep (fmap (\(n, ty) -> owlpretty n <> owlprettyTyAnnot ty <> comma) variants)) <> line <>
        owlpretty "}" <> line <> line <>
        owlpretty "impl" <+> owlpretty name <+> owlpretty "{" <> line <>
            indent 4 (vsep (fmap owlpretty implBlock)) <> line <>
        owlpretty "}" <> line <> line <>
        vsep (fmap owlpretty traitImpls)
