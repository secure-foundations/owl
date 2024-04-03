{-# LANGUAGE TemplateHaskell #-}
module Rust where
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Trans
import Control.Lens
import Data.Map.Strict as M

-- Loosely draws from MiniRust.ml in the KaRaMeL compiler
-- https://github.com/FStarLang/karamel/blob/master/lib/MiniRust.ml

data BorrowKind = RMut | RShared
    deriving (Eq, Ord, Show)

type RustName = String

data RustTy = 
      RTRef BorrowKind RustTy
    | RTVec RustTy
    | RTSlice RustTy
    | RTArray RustTy Int -- TODO: a way to specify const expression ints here?
    | RTTuple [RustTy]
    | RTOption RustTy
    | RTNamed RustName -- named types, eg structs, enums, etc
    | RTUnit
    | RTBool
    | RTU8
    | RTUsize
    deriving (Eq, Ord, Show)

type RustLet = (Bool, RustName, Maybe RustTy, RustExpr)

data RustExpr =
      RLet RustLet RustExpr -- bool is true if mutable
    | RIfThenElse RustExpr RustExpr RustExpr
    | RAssign RustName RustExpr
    | RCall (RustName, [RustExpr])
    | RVar RustName
    | RBorrow (BorrowKind, RustExpr)
    | RDeref RustExpr
    | RUnit
    | RUsizeLit Int
    -- TODO: loops, structs, enums, pattern-matching
    deriving (Eq, Ord, Show)

data RustFunc = RustFunc {
    rfName :: RustName,
    rfArgs :: [(RustName, RustTy)],
    rfRetTy :: RustTy,
    rfBody :: RustExpr
} deriving (Eq, Ord, Show)
makeLenses ''RustFunc

newtype RustTyDecl = RustTyDecl (RustName, RustTy)
    deriving (Eq, Ord, Show)

data RustTraitImpl = RustTraitImpl {
    rtiTraitName :: RustName,
    rtiForTy :: RustTy,
    rtiTraitTys :: [RustTyDecl],
    rtiTraitFuncs :: [RustFunc]
} deriving (Eq, Ord, Show)

data RustStructDecl = RustStructDecl {
    rStructName :: RustName,
    rStructFields :: [(RustName, RustTy)],
    rStructImplBlock :: [RustFunc],
    rStructTraitImpls :: [RustTraitImpl]
} deriving (Eq, Ord, Show)
makeLenses ''RustStructDecl

data RustEnumDecl = RustEnumDecl {
    rEnumName :: RustName,
    rEnumVariants :: [(RustName, Maybe RustTy)],
    rEnumImplBlock :: [RustFunc],
    rEnumTraitImpls :: [RustTraitImpl]
} deriving (Eq, Ord, Show)
makeLenses ''RustEnumDecl

-------------------------------------------------------------------
-- Helper functions

asRef :: RustName -> RustTy -> RustTy -> Maybe RustExpr
asRef name t1 t2 | t1 == t2 = 
    Just $ RVar name
asRef name t1 t2 | t2 == RTRef RShared t1 = 
    Just $ RBorrow (RShared, RVar name)
asRef name t1 t2 | t2 == RTRef RMut t1 = 
    Just $ RBorrow (RMut, RVar name)
asRef name (RTRef RMut t1) (RTRef RShared t2) | t1 == t2 = 
    Just $ RBorrow (RShared, RVar name)
asRef name (RTVec t1) (RTRef b (RTSlice t2)) | t1 == t2 = 
    Just $ RBorrow (b, RVar name)
asRef name t1 t2 = 
    Nothing
