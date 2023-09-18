{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
module AST where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Default (Default, def)
import Data.List
import Data.Maybe
import Control.Monad
import Control.Lens
import Data.Type.Equality
import Error.Diagnose.Position (Position)
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Unsafe
import Unbound.Generics.LocallyNameless.TH
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

-- localities are like "alice", "bob", "alice, bob", ...
type DefName = String -- For process definitions eg alice(..)
type ConstrName = String
type TableName = String
type TyVar = String

data Spanned a = Spanned { 
    _spanOf :: Ignore Position,
    _val :: a
                 }
    deriving (Generic, Typeable)

instance Show a => Show (Spanned a) where
    show (Spanned _ v) = show v

makeLenses ''Spanned



mkSpanned :: a -> Spanned a
mkSpanned x = Spanned (ignore def) x

mkSpannedWith :: Position -> a -> Spanned a
mkSpannedWith s x = Spanned (ignore s) x

type DataVar = Name AExpr
type IdxVar = Name Idx

-- Paths are used for localities, defs, names, and types
data Path = 
    PUnresolvedVar String
      | PUnresolvedPath String [String]
      | PRes ResolvedPath
    deriving (Generic, Typeable)

data PathVarType = OpenPathVar | ClosedPathVar (Ignore String)
    deriving (Show, Generic, Typeable)

instance Alpha PathVarType
instance Subst ResolvedPath PathVarType
instance Subst Idx PathVarType
instance Subst AExpr PathVarType

data ResolvedPath =
      PTop
      | PPathVar PathVarType (Name ResolvedPath) 
      | PDot ResolvedPath String
    deriving (Generic, Typeable)

topLevelPath :: String -> Path
topLevelPath s = PRes $ PDot PTop s

instance Show Path where
    show (PUnresolvedVar s) = "?" ++ s
    show (PUnresolvedPath s xs) = "?" ++ s ++ go xs
        where
            go [] = ""
            go (x:xs) = "." ++ x ++ go xs
    show (PRes p) = show p


instance Show ResolvedPath where
    show PTop = "Top"
    show (PDot (PPathVar OpenPathVar x) s) = "open(" ++ show x ++ ")." ++ s
    show (PPathVar (ClosedPathVar s) x) = "closed(" ++ unignore s ++ ", " ++ show x ++ ")"
    show (PPathVar OpenPathVar s) = "open(" ++ show s ++ ")"
    show (PDot x y) = show x ++ "." ++ y


data Idx = IVar (Ignore Position) IdxVar
    deriving (Show, Generic, Typeable)


mkIVar :: IdxVar -> Idx
mkIVar i = IVar (ignore def) i

data Endpoint = 
    Endpoint  EndpointVar
      | EndpointLocality Locality
    deriving (Show, Generic, Typeable)

type EndpointVar = Name Endpoint

data AExprX =
    AEVar (Ignore String) DataVar -- First argument is the user-facing name for the var
    | AEApp (Path) [FuncParam] [AExpr]
    | AEHex String
    | AEPreimage Path ([Idx], [Idx]) [AExpr]
    | AEGet NameExp
    | AEGetEncPK NameExp
    | AEGetVK NameExp
    | AEPackIdx Idx AExpr
    | AELenConst String
    | AEInt Int
    deriving (Show, Generic, Typeable)

type AExpr = Spanned AExprX


data NameExpX = 
    NameConst ([Idx], [Idx]) Path (Maybe ([AExpr], Int))
    | PRFName NameExp String
    deriving (Show, Generic, Typeable)

type NameExp = Spanned NameExpX

data Locality = Locality Path [Idx]
    deriving (Show, Generic, Typeable)



prfName :: NameExp -> String -> NameExp
prfName n ae = mkSpanned (PRFName n ae)

data LabelX =
    LName NameExp 
    | LZero
    | LAdv 
    | LTop
    | LJoin Label Label 
    | LConst LblConst -- Used Internally?
    | LRangeIdx (Bind IdxVar Label)
    deriving (Show, Generic, Typeable)

data LblConst = 
    TyLabelVar (Path)
    deriving (Show, Generic, Typeable)


type Label = Spanned LabelX

zeroLbl :: Label
zeroLbl = mkSpanned LZero

advLbl :: Label
advLbl = mkSpanned LAdv

topLbl :: Label
topLbl = mkSpanned LTop

nameLbl :: NameExp -> Label
nameLbl n = mkSpanned (LName n)

lblConst :: LblConst -> Label
lblConst s = mkSpanned (LConst s)


data PropX = 
    PTrue | PFalse | PAnd Prop Prop | POr Prop Prop
    | PNot Prop 
    | PEq AExpr AExpr 
    | PLetIn AExpr (Bind DataVar Prop)
    | PEqIdx Idx Idx
    | PImpl Prop Prop
    | PFlow Label Label 
    | PHappened Path ([Idx], [Idx]) [AExpr]
    | PQuantIdx Quant  (Bind IdxVar Prop)
    | PQuantBV Quant  (Bind DataVar Prop)
    | PIsConstant AExpr -- Internal use
    | PRO AExpr AExpr Int
    | PApp Path [Idx] [AExpr]
    | PAADOf NameExp AExpr
    deriving (Show, Generic, Typeable)


type Prop = Spanned PropX

data Quant = Forall | Exists
    deriving (Show, Generic, Typeable)

pAnd :: Prop -> Prop -> Prop
pAnd p1 p2 = mkSpanned (PAnd p1 p2)

pOr :: Prop -> Prop -> Prop
pOr p1 p2 = mkSpanned (POr p1 p2)

pImpl :: Prop -> Prop -> Prop
pImpl p1 p2 = mkSpanned (PImpl p1 p2)

pTrue :: Prop
pTrue = mkSpanned $ PTrue

pFalse :: Prop
pFalse = mkSpanned $ PFalse

pEq :: AExpr -> AExpr -> Prop
pEq x y = mkSpanned $ PEq x y

pNot :: Prop -> Prop
pNot p = mkSpanned $ PNot p

pFlow :: Label -> Label -> Prop
pFlow l1 l2 = mkSpanned $ PFlow l1 l2

pHappened :: Path -> ([Idx], [Idx]) -> [AExpr] -> Prop
pHappened s ids xs = mkSpanned $ PHappened s ids xs



data NameTypeX =
    NT_DH
    | NT_Sig Ty
    | NT_Nonce
    | NT_Enc Ty
    | NT_StAEAD Ty (Bind DataVar Prop) Path NoncePattern
    | NT_PKE Ty
    | NT_MAC Ty
    | NT_PRF [(String, (AExpr, NameType))]
    deriving (Show, Generic, Typeable)


type NameType = Spanned NameTypeX

-- Nonce patterns are injective contexts
data NoncePattern = NPHere
    deriving (Show, Generic, Typeable)

data TyX = 
    TData Label Label (Ignore (Maybe String))
    | TDataWithLength Label AExpr
    | TRefined Ty String (Bind DataVar Prop)
    | TOption Ty
    | TCase Prop Ty Ty
    | TConst (Path) [FuncParam]
    | TBool Label
    | TUnion Ty Ty
    | TUnit
    | TName NameExp -- Singleton type
    | TVK NameExp -- Singleton type
    | TDH_PK NameExp -- Singleton type
    | TEnc_PK NameExp -- Singleton type
    | TSS NameExp NameExp -- Singleton type
    | TAdmit -- return type of admit 
    | TExistsIdx (Bind IdxVar Ty) -- Label of which idx I am is adversary
    deriving (Show, Generic, Typeable)


type Ty = Spanned TyX

tData :: Label -> Label -> Ty
tData l1 l2 = mkSpanned $ TData l1 l2 (ignore Nothing)

tDataAnn :: Label -> Label -> String -> Ty
tDataAnn l1 l2 s = mkSpanned $ TData l1 l2 (ignore $ Just s)


tDataWithLength :: Label -> AExpr -> Ty
tDataWithLength l a = mkSpanned $ TDataWithLength l a

tUnit :: Ty
tUnit = mkSpanned TUnit




tName :: NameExp -> Ty
tName t = mkSpanned (TName t)

tAdmit :: Ty
tAdmit = mkSpanned TAdmit

tExistsIdx :: (Bind IdxVar Ty) -> Ty
tExistsIdx t = mkSpanned (TExistsIdx t)

data ModuleExpX = 
    ModuleBody IsModuleType (Bind (Name ResolvedPath) [Decl]) -- (Maybe ModuleExp)
      | ModuleVar Path
      | ModuleApp ModuleExp Path
      | ModuleFun (Bind (Name ResolvedPath, String, Embed ModuleExp) ModuleExp)
      deriving (Show, Generic, Typeable)

type ModuleExp = Spanned ModuleExpX

-- Decls are surface syntax
data DeclX = 
    DeclName String (Bind ([IdxVar], [IdxVar]) NameDecl) 
      | DeclSMTOption String String   
    | DeclDefHeader String (Bind ([IdxVar], [IdxVar]) Locality)
    | DeclPredicate String (Bind ([IdxVar], [DataVar]) Prop)
    | DeclFun       String (Bind (([IdxVar], [IdxVar]), [DataVar]) AExpr)
    | DeclDef String (Bind ([IdxVar], [IdxVar]) (
                         Locality,
                         Bind [(DataVar, Embed Ty)]
                          (
                            Maybe Prop,
                            Ty,
                            Maybe Expr
                          )
                        ))
    | DeclEnum String (Bind [IdxVar] [(String, Maybe Ty)]) -- Int is arity of indices
    | DeclInclude String
    | DeclCounter String (Bind ([IdxVar], [IdxVar]) Locality) 
    | DeclStruct String (Bind [IdxVar] [(String, Ty)]) -- Int is arity of indices
    | DeclTy String (Maybe Ty)
    | DeclDetFunc String DetFuncOps Int
    | DeclTable String Ty Locality -- Only valid for localities without indices, for now
    | DeclCorr (Bind ([IdxVar], [DataVar]) (Label, Label))
    | DeclLocality String (Either Int Path)
    | DeclModule String IsModuleType ModuleExp (Maybe ModuleExp) 
    deriving (Show, Generic, Typeable)

type Decl = Spanned DeclX

data ROStrictness = ROStrict (Maybe [Int]) | ROUnstrict
    deriving (Show, Generic, Typeable, Eq)

data NameDecl = 
    DeclBaseName NameType [Locality]
      | DeclRO ROStrictness (Bind [DataVar] (AExpr, Prop, [NameType], Expr)) 
      | DeclAbstractName
      deriving (Show, Generic, Typeable)

data IsModuleType = ModType | ModConcrete
    deriving (Show, Generic, Typeable, Eq)

instance Alpha IsModuleType
instance Subst AExpr IsModuleType
instance Subst ResolvedPath IsModuleType

data DetFuncOps =
    UninterpFunc
    deriving (Show, Generic, Typeable)



aeVar :: String -> AExpr
aeVar s = mkSpanned (AEVar (ignore s) (s2n s))

aeVar' :: DataVar -> AExpr
aeVar' v = mkSpanned $ AEVar (ignore $ show v) v

aeApp :: Path -> [FuncParam] -> [AExpr] -> AExpr
aeApp x y z = mkSpanned $ AEApp x y z

builtinFunc :: String -> [AExpr] -> AExpr
builtinFunc s xs = aeApp (PRes $ PDot PTop s) [] xs

aeLength :: AExpr -> AExpr
aeLength x = aeApp (PRes $ PDot PTop "length") [] [x]

aeLenConst :: String -> AExpr
aeLenConst s = mkSpanned $ AELenConst s 


aeTrue :: AExpr
aeTrue = mkSpanned (AEApp (topLevelPath "true") [] [])

data ExprX = 
    EInput String (Bind (DataVar, EndpointVar) Expr)
    | EOutput AExpr (Maybe Endpoint)
    -- The string is the name for the var
    -- If this binding is generated by ANF, the (Maybe AExpr) contains the AExpr from which it was generated
    | ELet Expr (Maybe Ty) (Maybe AExpr) String (Bind DataVar Expr) 
    | EBlock Expr -- Boundary for scoping; introduced by { }
    | EUnionCase AExpr String (Bind DataVar Expr)
    | EUnpack AExpr (Bind (IdxVar, DataVar) Expr)
    | EChooseIdx (Bind IdxVar Prop) (Bind IdxVar Expr)                                         
    | EIf AExpr Expr Expr
    | EForallBV (Bind DataVar Expr)
    | EForallIdx (Bind IdxVar Expr)
    | EGuard AExpr Expr
    | ERet AExpr
    | EGetCtr Path ([Idx], [Idx])
    | EIncCtr Path ([Idx], [Idx])
    | EDebug DebugCommand
    | ESetOption String String Expr
    | EAssert Prop
    | EAssume Prop
    | EAdmit
    | ECrypt CryptOp [AExpr]
    | ECall Path ([Idx], [Idx]) [AExpr]
    | ECase Expr [(String, Either Expr (Ignore String, Bind DataVar Expr))] -- The (Ignore String) part is the name for the var
    | EPCase Prop (Maybe Prop) Expr
    | EFalseElim Expr
    | ETLookup Path AExpr
    | ETWrite Path AExpr AExpr
    deriving (Show, Generic, Typeable)

type Expr = Spanned ExprX

type ROHint = (Path, ([Idx], [Idx]), [AExpr])

data CryptOp = 
    CHash [ROHint] Int
      | CPRF String
      | CLemma BuiltinLemma
      | CAEnc 
      | CADec 
      | CEncStAEAD Path ([Idx], [Idx])
      | CDecStAEAD
      | CPKEnc
      | CPKDec
      | CMac
      | CMacVrfy
      | CSign
      | CSigVrfy
    deriving (Show, Generic, Typeable)

data BuiltinLemma = 
      LemmaCRH 
      | LemmaConstant 
      | LemmaDisjNotEq 
      | LemmaCrossDH NameExp NameExp NameExp
    deriving (Show, Generic, Typeable)



data DebugCommand = 
    DebugPrintTyOf AExpr
      | DebugResolveANF AExpr
      | DebugPrint String
      | DebugPrintTy Ty
      | DebugPrintProp Prop
      | DebugPrintTyContext Bool
      | DebugPrintExpr Expr
      | DebugPrintLabel Label
      | DebugPrintModules
    deriving (Show, Generic, Typeable)

data FuncParam = 
      ParamAExpr AExpr
      | ParamStr String
      | ParamLbl Label
      | ParamTy Ty
      | ParamIdx Idx
      | ParamName NameExp
      deriving (Show, Generic, Typeable)


-- LocallyNameless instances

$(makeClosedAlpha ''Position)

instance Subst b Position

instance Alpha a => Alpha (Spanned a)

instance Subst b a => Subst b (Spanned a)

instance Alpha Idx
instance Alpha Endpoint
instance Subst Idx Idx where
    isvar (IVar _ v) = Just (SubstName v)
instance Subst AExpr Idx
instance Subst ResolvedPath Idx

instance Subst AExpr Endpoint
instance Subst ResolvedPath Endpoint

instance Alpha NameDecl
instance Subst AExpr NameDecl
instance Subst ResolvedPath NameDecl

instance Alpha ROStrictness
instance Subst AExpr ROStrictness
instance Subst ResolvedPath ROStrictness

instance Alpha DeclX
instance Subst ResolvedPath DeclX

instance Alpha ModuleExpX
instance Subst ResolvedPath ModuleExpX

instance Alpha AExprX
instance Subst Idx AExprX
instance Subst ResolvedPath AExprX
instance Subst AExpr AExprX where
    isCoerceVar (AEVar _ v) = Just (SubstCoerce v (\x -> Just (_val x)))
    isCoerceVar _ = Nothing

instance Alpha NameExpX
instance Subst Idx NameExpX
instance Subst AExpr NameExpX
instance Subst ResolvedPath NameExpX

instance Alpha NameTypeX
instance Subst Idx NameTypeX
instance Subst AExpr NameTypeX
instance Subst ResolvedPath NameTypeX

instance Alpha NoncePattern
instance Subst Idx NoncePattern
instance Subst AExpr NoncePattern
instance Subst ResolvedPath NoncePattern

instance Alpha FuncParam
instance Subst Idx FuncParam
instance Subst AExpr FuncParam
instance Subst ResolvedPath FuncParam

instance Alpha LabelX
instance Subst Idx LabelX
instance Subst AExpr LabelX
instance Subst ResolvedPath LabelX

instance Alpha LblConst
instance Subst Idx LblConst
instance Subst AExpr LblConst
instance Subst ResolvedPath LblConst

instance Alpha DetFuncOps
instance Subst ResolvedPath DetFuncOps

instance Alpha Path
instance Subst Idx Path
instance Subst AExpr Path
instance Subst ResolvedPath Path where

instance Alpha ResolvedPath
instance Subst ResolvedPath ResolvedPath where
    isvar (PPathVar _ v) = Just (SubstName v)
    isvar _ = Nothing
instance Subst AExpr ResolvedPath
instance Subst Idx ResolvedPath

instance Alpha TyX
instance Subst Idx TyX
instance Subst AExpr TyX
instance Subst ResolvedPath TyX

instance Alpha PropX
instance Subst Idx PropX
instance Subst AExpr PropX
instance Subst ResolvedPath PropX

tRefined :: Ty -> String -> Prop -> Ty 
tRefined t s p = mkSpanned $ TRefined t s $ bind (s2n s) p

instance Alpha Quant
instance Subst Idx Quant
instance Subst AExpr Quant
instance Subst ResolvedPath Quant


instance Alpha DebugCommand
instance Subst AExpr DebugCommand
instance Subst ResolvedPath DebugCommand

instance Alpha Locality
instance Subst Idx Locality
instance Subst AExpr Locality
instance Subst ResolvedPath Locality

instance Alpha ExprX
instance Subst AExpr ExprX
instance Subst Idx ExprX
instance Subst Idx Endpoint
instance Subst Idx DebugCommand
instance Subst ResolvedPath ExprX

instance Alpha CryptOp
instance Subst AExpr CryptOp
instance Subst Idx CryptOp
instance Subst ResolvedPath CryptOp

instance Alpha BuiltinLemma
instance Subst AExpr BuiltinLemma
instance Subst Idx BuiltinLemma
instance Subst ResolvedPath BuiltinLemma




-- Wrapper datatype for native comparison up to alpha equivalence. Used for
-- indexing maps by ASTs 
newtype AlphaOrd a = AlphaOrd { _unAlphaOrd :: a }

instance Alpha a => Eq (AlphaOrd a) where
    (AlphaOrd x) == (AlphaOrd y) = (x `aeq` y)

instance Alpha a => Ord (AlphaOrd a) where
    compare (AlphaOrd x) (AlphaOrd y) = (x `acompare` y)


tLemma :: Prop -> Ty
tLemma p = tRefined tUnit "._" p 

