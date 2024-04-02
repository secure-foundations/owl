module Rust where
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Trans
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
    | RTUnit
    | RTBool
    | RTU8
    | RTUsize
    -- TODO: structs, enums
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
