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
import Prettyprinter
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
    deriving (Show, Generic, Typeable)

makeLenses ''Spanned

instance Pretty a => Pretty (Spanned a) where
    pretty (Spanned _ v) = pretty v


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
    | AEPreimage Path ([Idx], [Idx])
    | AEGet NameExp
    | AEGetEncPK NameExp
    | AEGetVK NameExp
    | AEPackIdx Idx AExpr
    | AELenConst String
    | AEInt Int
    deriving (Show, Generic, Typeable)

type AExpr = Spanned AExprX


data NameExpX = 
    NameConst ([Idx], [Idx]) Path (Maybe Int)
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
    TData Label Label
    | TDataWithLength Label AExpr
    | TRefined Ty (Bind DataVar Prop)
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
tData l1 l2 = mkSpanned $ TData l1 l2

tDataWithLength :: Label -> AExpr -> Ty
tDataWithLength l a = mkSpanned $ TDataWithLength l a

tUnit :: Ty
tUnit = mkSpanned TUnit


tRefined :: Ty -> Bind DataVar Prop -> Ty
tRefined t p = mkSpanned $ TRefined t p


tName :: NameExp -> Ty
tName t = mkSpanned (TName t)

tAdmit :: Ty
tAdmit = mkSpanned TAdmit

tExistsIdx :: (Bind IdxVar Ty) -> Ty
tExistsIdx t = mkSpanned (TExistsIdx t)
-- tRefined :: Ty -> Var -> Prop -> Ty
-- tRefined t x p = mkSpanned $ TRefined t x p

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
    | DeclCorr (Bind [IdxVar] (Label, Label))
    | DeclLocality String (Either Int Path)
    | DeclModule String IsModuleType ModuleExp (Maybe ModuleExp) 
    deriving (Show, Generic, Typeable)

type Decl = Spanned DeclX

data NameDecl = 
    DeclBaseName NameType [Locality]
      | DeclRO [AExpr] [NameType] (Maybe Expr)
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
aeTrue = mkSpanned (AEApp (topLevelPath "TRUE") [] [])

data ExprX = 
    EInput (Bind (DataVar, EndpointVar) Expr)
    | EOutput AExpr (Maybe Endpoint)
    -- The string is the name for the var
    -- If this binding is generated by ANF, the (Ignore (Maybe AExpr)) contains the AExpr from which it was generated
    | ELet Expr (Maybe Ty) (Ignore (Maybe AExpr)) String (Bind DataVar Expr) 
    | EUnionCase AExpr (Bind DataVar Expr)
    | EUnpack AExpr (Bind (IdxVar, DataVar) Expr)
    | EChooseIdx (Bind IdxVar Prop) (Bind IdxVar Expr)                                         
    | EIf AExpr Expr Expr
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

data CryptOp = 
    CHash Path ([Idx], [Idx]) Int
      | CPRF String
      | CCRHLemma AExpr AExpr
      | CConstantLemma AExpr
      | CDisjNotEq AExpr AExpr
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



data DebugCommand = 
    DebugPrintTyOf AExpr
      | DebugPrint String
      | DebugPrintTy Ty
      | DebugPrintProp Prop
      | DebugPrintTyContext
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
--- Pretty instances ---

instance Pretty (Name a) where
    pretty v = pretty $ show v

instance Pretty Idx where
    pretty (IVar _ s) = pretty s

prettyIdxParams :: ([Idx], [Idx]) -> Doc ann
prettyIdxParams  ([], []) = mempty
prettyIdxParams (vs1, vs2) = pretty "<" <> pretty (intercalate "," (map (show . pretty) vs1)) <> pretty "@" <> pretty (intercalate "," (map (show . pretty) vs2)) <> pretty ">"

instance Pretty NameExpX where
    pretty (PRFName n e) = pretty "PRF<" <> pretty n <> pretty ", " <> pretty e <> pretty ">"
    pretty (NameConst vs n oi) = 
        let pi = case oi of
                   Nothing -> mempty
                   Just i -> pretty "[" <> pretty i <> pretty "]"
        in
        pretty n <> prettyIdxParams vs <> pi

prettyBind :: (Alpha a, Alpha b, Pretty a, Pretty b) => Bind b a -> (Doc ann, Doc ann)
prettyBind b = 
    let (x, y) = unsafeUnbind b in
    (pretty x, pretty y)

instance Pretty LblConst where
    pretty (TyLabelVar s) = pretty s

instance Pretty LabelX where
    pretty (LName n) = pretty "[" <> pretty n <> pretty "]"
    pretty LZero = pretty "static"
    pretty (LAdv) = pretty "adv"
    pretty (LJoin v1 v2) = pretty v1 <+> pretty "/\\" <+> pretty v2
    pretty (LConst s) = pretty s
    pretty (LRangeIdx l) = 
        let (b, l') = prettyBind l in
        pretty "/\\_" <> b <+> pretty "(" <> l' <> pretty ")"

instance Pretty (Path) where
    pretty x = pretty $ show x

instance Pretty TyX where
    pretty TUnit =
        pretty "unit"
    pretty (TBool l) = 
            pretty "Bool<" <+> pretty l <> pretty ">"
    pretty (TData l1 l2) = 
            if l1 `aeq` l2 then
                pretty "Data" <+> angles (pretty l1)
            else
                pretty "Data <" <> pretty l1 <> pretty ", |" <> pretty l2 <> pretty "|>"
    pretty (TDataWithLength l1 a) = 
            pretty "Data <" <> pretty l1 <> pretty ">" <+> pretty "|" <> pretty a <> pretty "|"
    pretty (TRefined t xp) = 
        let (x, p) = prettyBind xp in
        x <> pretty ":" <> parens (pretty t) <> braces p
    pretty (TOption t) = 
            pretty "Option" <+> pretty t
    pretty (TCase p t1 t2) = 
            pretty "if" <+> pretty p <+> pretty "then" <+> pretty t1 <> pretty " else " <> pretty t2 
    pretty (TConst n ps) =
            pretty n <> pretty "<" <> pretty (intercalate "," (map (show . pretty) ps)) <> pretty ">"
    pretty (TName n) =
            pretty "Name(" <> pretty n <> pretty ")"
    pretty (TVK n) =
            pretty "vk(" <> pretty n <> pretty ")"
    pretty (TDH_PK n) =
            pretty "dhpk(" <> pretty n <> pretty ")"
    pretty (TEnc_PK n) =
            pretty "encpk(" <> pretty n <> pretty ")"
    pretty (TSS n m) =
            pretty "shared_secret(" <> pretty n <> pretty ", " <> pretty m <> pretty ")"
    pretty TAdmit = pretty "admit"
    pretty (TExistsIdx it) = 
        let (i, t) = prettyBind it in
        pretty "exists" <+> i <> pretty "." <+> t
    pretty (TUnion t1 t2) =
        pretty "Union<" <> pretty t1 <> pretty "," <> pretty t2 <> pretty ">"

instance Pretty Quant where
    pretty Forall = pretty "forall"
    pretty Exists = pretty "exists"

instance Pretty PropX where 
    pretty PTrue = pretty "true"
    pretty PFalse = pretty "false"
    pretty (PAnd p1 p2) = pretty p1 <+> pretty "&&" <+> pretty p2
    pretty (POr p1 p2) = pretty p1 <+> pretty "||" <+> pretty p2
    pretty (PNot p) = pretty "!" <+> pretty p
    pretty (PEq e1 e2) = pretty e1 <+> pretty "=" <+> pretty e2
    pretty (PEqIdx e1 e2) = pretty e1 <+> pretty "=idx" <+> pretty e2
    pretty (PLetIn a xe2) = 
        let (x, e2) = prettyBind xe2 in
        pretty "let" <+> x <+> pretty "=" <+> pretty a <+> pretty "in" <+> e2
    pretty (PImpl p1 p2) = pretty p1 <+> pretty "==>" <+> pretty p2
    pretty (PFlow l1 l2) = pretty l1 <+> pretty "<=" <+> pretty l2
    pretty (PIsConstant a) = pretty "is_constant(" <> pretty a <> pretty ")"
    pretty (PQuantIdx q b) = 
        let (x, p) = prettyBind b in
        pretty q <+> x <+> pretty ": idx" <> pretty "." <+> p
    pretty (PQuantBV q b) = 
        let (x, p) = prettyBind b in
        pretty q <+> x <+> pretty ": bv" <> pretty "." <+> p
    pretty (PRO a b i) = pretty "ro(" <> pretty a <> pretty "," <+> pretty b <> pretty "," <+> pretty i <> pretty ")"
    pretty (PApp p is xs) = pretty p <> angles (mconcat $ map pretty is) <> list (map pretty xs)
    pretty (PHappened s ixs xs) = 
        let pids = 
                case ixs of
                  ([], []) -> mempty
                  (v1, v2) -> pretty "<" <> 
                         pretty (intercalate "," (map (show . pretty) v1)) <> 
                         pretty "@" <>
                         pretty (intercalate "," (map (show . pretty) v2)) <> 
                         pretty ">" in 
        pretty "happened(" <> pretty s <> pids <> tupled (map pretty xs) <> pretty ")"

instance Pretty NameTypeX where
    pretty (NT_Sig ty) = pretty "sig" <+> pretty ty
    pretty (NT_StAEAD ty xaad p pat) = 
        let (x, aad) = prettyBind xaad in
        pretty "StAEAD" <+> pretty ty <+> pretty "(" <> x <> pretty "." <> aad <> pretty ")" <+> pretty p
    pretty (NT_Enc ty) = pretty "enc" <+> pretty ty
    pretty (NT_PKE ty) = pretty "pke" <+> pretty ty
    pretty (NT_MAC ty) = pretty "mac" <+> pretty ty
    pretty (NT_PRF xs) = pretty "prf" <+> pretty "[" <> mconcat (map (\(ae, nt) -> pretty ae <+> pretty "->" <+> pretty nt) xs) <> pretty "]"
    pretty NT_DH = pretty "DH"
    pretty NT_Nonce = pretty "nonce"


instance Pretty AExprX where
    pretty (AEVar s n) = pretty (unignore s)
    pretty (AEApp f _ as) = pretty f <> tupled (map pretty as)
    pretty (AEHex s) = pretty "0x" <> pretty s
    pretty (AELenConst s) = pretty "|" <> pretty s <> pretty "|"
    pretty (AEInt i) = pretty i
    pretty (AEPreimage p ps) = pretty "preimage" <> prettyIdxParams ps <> pretty "(" <> pretty p <> pretty ")"
    pretty (AEGet ne) = pretty "get" <> pretty "(" <> pretty ne <> pretty ")"
    pretty (AEGetEncPK ne) = pretty "get_encpk" <> pretty "(" <> pretty ne <> pretty ")"
    pretty (AEGetVK ne) = pretty "get_vk" <> pretty "(" <> pretty ne <> pretty ")"
    pretty (AEPackIdx s a) = pretty "pack" <> pretty "<" <> pretty s <> pretty ">(" <> pretty a <> pretty ")"

instance Pretty CryptOp where
    pretty (CHash p (is, ps) i) = 
        pretty "RO" <+> pretty p <+> pretty is <+> pretty ps <+> pretty i
    pretty (CPRF x) = 
        pretty "PRF" <+> pretty x 
    pretty (CConstantLemma a) = pretty "is_constant_lemma<" <> pretty a <> pretty ">()"
    pretty (CDisjNotEq a1 a2) = pretty "disjoint_not_eq<" <> pretty a1 <> pretty "," <> pretty a2 <> pretty ">()"
    pretty (CAEnc) = pretty "aenc"
    pretty (CADec) = pretty "adec"
    pretty CPKEnc = pretty "pkenc"
    pretty CPKDec = pretty "pkdec"
    pretty CMac = pretty "mac"
    pretty CMacVrfy = pretty "mac_vrfy"
    pretty CSign = pretty "sign"
    pretty CSigVrfy = pretty "vrfy"
    pretty (CCRHLemma a1 a2) = pretty "crh_lemma" <> angles (tupled [pretty a1, pretty a2])
    pretty (CEncStAEAD p (idx1, idx2)) = pretty "st_aead_enc" <> angles (pretty p <> angles (tupled (map pretty idx1) <> pretty "@" <> tupled (map pretty idx2)))
    pretty (CDecStAEAD) = pretty "st_aead_dec"

instance Pretty ExprX where 
    pretty (ECrypt cop as) = 
        pretty cop <> (tupled (map pretty as))
    pretty (EInput k) = 
        let ((x, i), e) = unsafeUnbind k in
        pretty "input" <+> pretty x <> pretty ", " <> pretty i <> pretty " in " <> pretty e
    pretty (EOutput e l) = pretty "output" <+> pretty e <+> (case l of
       Nothing -> pretty ""
       Just s -> pretty "to" <+> pretty s)
    pretty (ELet e1 tyAnn anf sx xk) = 
        let (x, k) = prettyBind xk in
        let tann = case tyAnn of
                     Nothing -> mempty
                     Just t -> pretty ":" <+> pretty t
        in
        let anfLet = case unignore anf of
                        Nothing -> pretty "let"
                        Just _ -> pretty "anf_let"
        in
        anfLet <+> pretty sx <+> tann <+> pretty "=" <+> pretty e1 <+> pretty "in" <> line <> k
    pretty (EUnionCase a xk) = 
        let (x, k) = prettyBind xk in
        pretty "union_case" <+> x <+> pretty "=" <> pretty a <+>  pretty "in" <+> k
    pretty (EUnpack a k) = pretty "unpack a .... TODO"
    pretty (EIf t e1 e2) = 
        pretty "if" <+> pretty t <+> pretty "then" <+> pretty e1 <+> pretty "else" <+> pretty e2
    pretty (EGuard a e) = 
        pretty "guard" <+> pretty a <+> pretty "in" <+> pretty e
    pretty (ERet ae) = pretty ae
    pretty (EAdmit) = pretty "admit"
    pretty (ECall f is as) = 
        let inds = case is of
                     ([], []) -> mempty
                     (v1, v2) -> pretty "<" <> mconcat (map pretty v1) <> pretty "@" <> mconcat (map pretty v2) <> pretty ">"
        in
        pretty "call" <> inds <+> pretty f <> tupled (map pretty as)
    pretty (ECase t xs) = 
        let pcases = 
                map (\(c, o) -> 
                    case o of
                      Left e -> pretty "|" <+> pretty c <+> pretty "=>" <+> pretty e
                      Right (_, xe) -> let (x, e) = prettyBind xe in pretty "|" <+> pretty c <+> x <+> pretty "=>" <+> e
                    ) xs in
        pretty "case" <+> pretty t <> line <> vsep pcases
    pretty (EPCase p op e) = 
        pretty "decide" <+> pretty p <+> pretty "in" <+> pretty e
    pretty (EDebug dc) = pretty "debug" <+> pretty dc
    pretty (ESetOption s1 s2 e) = pretty "set_option" <+> pretty (show s1) <+> pretty "=" <+> pretty (show s2) <+> pretty "in" <+> pretty e                                         
    pretty (EAssert p) = pretty "assert" <+> pretty p
    pretty (EAssume p) = pretty "assume" <+> pretty p
    pretty (EFalseElim k) = pretty "false_elim in" <+> pretty k
    pretty (ETLookup n a) = pretty "lookup" <> tupled [pretty a]
    pretty (ETWrite n a a') = pretty "write" <> tupled [pretty a, pretty a']
    pretty _ = pretty "unimp"

instance Pretty DebugCommand where
    pretty (DebugPrintTyOf ae) = pretty "debugPrintTyOf(" <> pretty ae <> pretty ")"
    pretty (DebugPrint s) = pretty "debugPrint(" <> pretty s <> pretty ")"
    pretty (DebugPrintTy t) = pretty "debugPrintTy(" <> pretty t <> pretty ")"
    pretty (DebugPrintProp t) = pretty "debugPrintProp(" <> pretty t <> pretty ")"
    pretty (DebugPrintTyContext) = pretty "debugPrintTyContext"
    pretty (DebugPrintExpr e) = pretty "debugPrintExpr(" <> pretty e <> pretty ")"
    pretty (DebugPrintLabel l) = pretty "debugPrintLabel(" <> pretty l <> pretty ")"

instance Pretty FuncParam where
    pretty (ParamStr s) = pretty s
    pretty (ParamAExpr a) = pretty a
    pretty (ParamLbl l) = pretty l
    pretty (ParamTy t) = pretty t
    pretty (ParamIdx i) = pretty i
    pretty (ParamName ne) = pretty ne

instance Pretty Endpoint where
    pretty (Endpoint  x) = pretty x
    pretty (EndpointLocality l) = pretty "endpoint(" <> pretty l <> pretty ")"

instance Pretty Locality where
    pretty (Locality s xs) = pretty s <> angles (mconcat $ map pretty xs)

instance Pretty DeclX where
    pretty d = pretty (show d)

instance Pretty ModuleExpX where
    pretty (ModuleBody _ nk) = 
        let (n, k) = prettyBind nk in
        angles (n <> pretty "." <> k)
    pretty (ModuleVar p) = pretty p
    pretty x = pretty $ show x


-- Wrapper datatype for native comparison up to alpha equivalence. Used for
-- indexing maps by ASTs 
newtype AlphaOrd a = AlphaOrd { _unAlphaOrd :: a }

instance Alpha a => Eq (AlphaOrd a) where
    (AlphaOrd x) == (AlphaOrd y) = (x `aeq` y)

instance Alpha a => Ord (AlphaOrd a) where
    compare (AlphaOrd x) (AlphaOrd y) = (x `acompare` y)


tLemma :: Prop -> Ty
tLemma p = tRefined tUnit (bind (s2n "._") p)

