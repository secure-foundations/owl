{-# LANGUAGE TemplateHaskell #-}
module Verus where
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

type VerusName = String

data VerusTy = 
      RTRef BorrowKind VerusTy
    | RTVec VerusTy
    | RTSlice VerusTy
    | RTArray VerusTy Int -- TODO: a way to specify const expression ints here?
    | RTTuple [VerusTy]
    | RTOption VerusTy
    | RTNamed VerusName -- named types, eg structs, enums, etc
    | RTUnit
    | RTBool
    | RTU8
    | RTUsize
    deriving (Eq, Ord, Show)

type VerusLet = (Bool, VerusName, Maybe VerusTy, VerusExpr)

data VerusExpr =
      RLet VerusLet VerusExpr -- bool is true if mutable
    | RIfThenElse VerusExpr VerusExpr VerusExpr
    | RAssign VerusName VerusExpr
    | RCall (VerusName, [VerusExpr])
    | RVar VerusName
    | RBorrow (BorrowKind, VerusExpr)
    | RDeref VerusExpr
    | RUnit
    | RUsizeLit Int
    -- TODO: loops, structs, enums, pattern-matching
    deriving (Eq, Ord, Show)

data VerusFunc = VerusFunc {
    rfName :: VerusName,
    rfArgs :: [(VerusName, VerusTy)],
    rfRetTy :: VerusTy,
    rfBody :: VerusExpr
} deriving (Eq, Ord, Show)
makeLenses ''VerusFunc

newtype VerusTyDecl = VerusTyDecl (VerusName, VerusTy)
    deriving (Eq, Ord, Show)

data VerusTraitImpl = VerusTraitImpl {
    rtiTraitName :: VerusName,
    rtiForTy :: VerusTy,
    rtiTraitTys :: [VerusTyDecl],
    rtiTraitFuncs :: [VerusFunc]
} deriving (Eq, Ord, Show)

data VerusStructDecl = VerusStructDecl {
    rStructName :: VerusName,
    rStructFields :: [(VerusName, VerusTy)],
    rStructImplBlock :: [VerusFunc],
    rStructTraitImpls :: [VerusTraitImpl]
} deriving (Eq, Ord, Show)
makeLenses ''VerusStructDecl

data VerusEnumDecl = VerusEnumDecl {
    rEnumName :: VerusName,
    rEnumVariants :: [(VerusName, Maybe VerusTy)],
    rEnumImplBlock :: [VerusFunc],
    rEnumTraitImpls :: [VerusTraitImpl]
} deriving (Eq, Ord, Show)
makeLenses ''VerusEnumDecl

-------------------------------------------------------------------
-- Helper functions

asRef :: VerusName -> VerusTy -> VerusTy -> Maybe VerusExpr
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
