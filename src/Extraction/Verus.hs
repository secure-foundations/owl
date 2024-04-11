{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
module Verus where
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Trans
import Control.Lens
import Data.Map.Strict as M
import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

-- Loosely draws from MiniRust.ml in the KaRaMeL compiler
-- https://github.com/FStarLang/karamel/blob/master/lib/MiniRust.ml

data BorrowKind = RMut | RShared
    deriving (Eq, Ord, Show, Generic, Typeable)

newtype Lifetime = Lifetime String
    deriving (Eq, Ord, Show, Generic, Typeable)

-- data VerusName = VN String (Maybe Lifetime)
--    deriving (Eq, Ord, Show)

type VerusName = String

data ConstUsize =
    CUsizeLit Int
    | CUsizeConst String
    | CUsizePlus ConstUsize ConstUsize
    deriving (Eq, Ord, Show, Generic, Typeable)

data VerusTy = 
      RTRef BorrowKind VerusTy
    | RTVec VerusTy
    | RTSlice VerusTy
    | RTArray VerusTy ConstUsize -- TODO: a way to specify const expression ints here?
    | RTTuple [VerusTy]
    | RTOption VerusTy
    | RTNamed VerusName -- named types, eg structs, enums, etc
    | RTParam VerusName [VerusTy] -- general-purpose parameterized types (we special-case Option and Vec)
    | RTWithLifetime VerusTy Lifetime
    | RTOwlBuf Lifetime
    | RTUnit
    | RTBool
    | RTU8
    | RTUsize
    | RTVerusGhost
    deriving (Eq, Ord, Show, Generic, Typeable)

instance Alpha BorrowKind
instance Alpha Lifetime
instance Alpha ConstUsize
instance Alpha VerusTy

type VerusLet = (Bool, VerusName, Maybe VerusTy, VerusExpr) -- bool is true if mutable

data VerusExpr =
      RLet VerusLet VerusExpr
    | RIfThenElse VerusExpr VerusExpr VerusExpr
    | RAssign VerusName VerusExpr
    | RCall VerusName [VerusExpr]
    | RDotCall VerusExpr VerusName [VerusExpr] -- `RDotCall (v, f, args)` is `v.f(args)`
    | RFieldSel VerusExpr VerusName -- `RFieldSel (v, i)` is `v.i` for struct/tuple dereference
    | RVar VerusName
    | RBorrow BorrowKind VerusExpr
    | RDeref VerusExpr
    | RInfixOp VerusExpr String VerusExpr 
    | RUnit
    | RUsizeLit Int
    | RBoolLit Bool
    | RStructLit VerusName [(VerusName, VerusExpr)]
    -- TODO: loops, structs, enums, pattern-matching
    deriving (Eq, Ord, Show)

data VerusFuncMode = VOpenSpec | VClosedSpec | VProof | VExec 
    deriving (Eq, Ord, Show)

-- For use in `requires` and `ensures`; we just use VerusExpr for bodies of spec fns
data VerusSpecExpr =
    --  VSLet VerusLet VerusSpecExpr -- bool is true if mutable
      VSIfThenElse VerusSpecExpr VerusSpecExpr VerusSpecExpr
    | VSCall VerusName [VerusSpecExpr]
    | VSDotCall VerusName VerusName [VerusSpecExpr] -- `RDotCall (v, f, args)` is `v.f(args)`
    | VSVar VerusName
    | VSDeref VerusSpecExpr
    | VSFieldSel VerusSpecExpr VerusName
    | VSInfixOp VerusSpecExpr String VerusSpecExpr 
    | VSUnit
    | VSUsizeLit Int
    | VSBoolLit Bool
    -- Special Verus syntax
    | VSSpecImplies VerusSpecExpr VerusSpecExpr -- `VSSpecImplies (e1, e2)` is `e1 ==> e2`
    | VSSpecMatches VerusSpecExpr VerusSpecExpr -- `VSSpecMatches (e1, e2)` is `e1 matches e2`
    | VSSpecArrow VerusSpecExpr VerusName -- `VSSpecArrow (e1, e2)` is `e1->e2`
    deriving (Eq, Ord, Show)

data VerusArg =
      SelfArg BorrowKind
    | Arg VerusName VerusTy
    deriving (Eq, Ord, Show)

data VerusFunc = VerusFunc {
    rfName :: VerusName,
    rfMode :: VerusFuncMode,
    rfExternalBody :: Bool, -- if true, add #[verifier(external_body)]
    rfVerifierOpaque :: Bool,
    rfArgs :: [VerusArg],
    rfRetTy :: VerusTy,
    rfRequires :: [VerusSpecExpr],
    rfEnsures :: [VerusSpecExpr],
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
    Just $ RBorrow RShared (RVar name)
asRef name t1 t2 | t2 == RTRef RMut t1 = 
    Just $ RBorrow RMut (RVar name)
asRef name (RTRef RMut t1) (RTRef RShared t2) | t1 == t2 = 
    Just $ RBorrow RShared (RVar name)
asRef name (RTVec t1) (RTRef b (RTSlice t2)) | t1 == t2 = 
    Just $ RBorrow b (RVar name)
asRef name t1 t2 = 
    Nothing

-- nl :: String -> VerusName
-- nl s = VN s Nothing

-- withLifetime :: String -> String -> VerusName
-- withLifetime name lt = VN name $ Just (Lifetime lt)

-- rtResult :: VerusTy -> VerusTy -> VerusTy
-- rtResult t e = RTParam (nl "Result") [t, e]