{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
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
type FuncName = String -- For deterministic functions eg xor(*, *), 
type DistrName = String -- For probabilistic functions eg senc
type DefName = String -- For process definitions eg alice(..)
type ConstrName = String
type TyName = String
type TableName = String

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
    | AEApp FuncName [FuncParam] [AExpr]
    | AEString String
    | AEGet NameExp
    | AEGetEncPK NameExp
    | AEGetVK NameExp
    | AEPackIdx Idx AExpr
    | AELenConst String
    | AEInt Int
    deriving (Show, Generic, Typeable)

type AExpr = Spanned AExprX


data NameExpX = 
    BaseName ([Idx], [Idx]) String
    | ROName String
    | PRFName NameExp String
    deriving (Show, Generic, Typeable)


type NameExp = Spanned NameExpX

data Locality = Locality String [Idx]
    deriving (Show, Generic, Typeable)





roName :: String -> NameExp
roName s = mkSpanned (ROName s)

prfName :: NameExp -> String -> NameExp
prfName n ae = mkSpanned (PRFName n ae)

data LabelX =
    LName NameExp 
    | LZero
    | LAdv 
    | LJoin Label Label 
    | LVar String -- Used Internally?
    | LRangeIdx (Bind IdxVar Label)
    deriving (Show, Generic, Typeable)


type Label = Spanned LabelX

zeroLbl :: Label
zeroLbl = mkSpanned LZero

advLbl :: Label
advLbl = mkSpanned LAdv

nameLbl :: NameExp -> Label
nameLbl n = mkSpanned (LName n)

varLbl :: String -> Label
varLbl s = mkSpanned (LVar s)


data PropX = 
    PTrue | PFalse | PAnd Prop Prop | POr Prop Prop
    | PNot Prop 
    | PEq AExpr AExpr 
    | PEqIdx Idx Idx
    | PImpl Prop Prop
    | PFlow Label Label 
    | PHappened String ([Idx], [Idx]) [AExpr]
    deriving (Show, Generic, Typeable)


type Prop = Spanned PropX

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

pHappened :: String -> ([Idx], [Idx]) -> [AExpr] -> Prop
pHappened s ids xs = mkSpanned $ PHappened s ids xs



data NameTypeX =
    NT_DH
    | NT_Sig Ty
    | NT_Nonce
    | NT_Enc Ty
    | NT_PKE Ty
    | NT_MAC Ty
    | NT_PRF [(String, (AExpr, NameType))]
    deriving (Show, Generic, Typeable)


type NameType = Spanned NameTypeX

data TyX = 
    TData Label Label
    | TDataWithLength Label AExpr
    | TRefined Ty (Bind DataVar Prop)
    | TOption Ty
    | TCase Prop Ty Ty
    | TVar TyName [FuncParam]
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

-- Decls are surface syntax
data DeclX = 
    DeclName String (Bind ([IdxVar], [IdxVar]) (Maybe (NameType, [Locality])))
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
    | DeclStruct String (Bind [IdxVar] [(String, Ty)]) -- Int is arity of indices
    | DeclTy String (Maybe Ty)
    | DeclDetFunc String DetFuncOps Int
    | DeclTable String Ty Locality -- Only valid for localities without indices, for now
    | DeclRandOrcl String [String] (AExpr, NameType)
    | DeclFlow Label Label 
    | DeclLocality String Int

type Decl = Spanned DeclX

data DetFuncOps =
    UninterpFunc



aeVar :: String -> AExpr
aeVar s = mkSpanned (AEVar (ignore s) (s2n s))

aeVar' :: DataVar -> AExpr
aeVar' v = mkSpanned $ AEVar (ignore $ show v) v

aeApp :: FuncName -> [FuncParam] -> [AExpr] -> AExpr
aeApp x y z = mkSpanned $ AEApp x y z

aeLength :: AExpr -> AExpr
aeLength x = aeApp "length" [] [x]

aeLenConst :: String -> AExpr
aeLenConst s = mkSpanned $ AELenConst s 


aeTrue :: AExpr
aeTrue = mkSpanned (AEApp "true" [] [])

data ExprX = 
    EInput (Bind (DataVar, EndpointVar) Expr)
    | EOutput AExpr (Maybe Endpoint)
    | ELet Expr (Maybe Ty) String (Bind DataVar Expr) -- The string is the name for the var
    | EUnionCase AExpr (Bind DataVar Expr)
    | EUnpack AExpr (Bind (IdxVar, DataVar) Expr)
    | ESamp DistrName [AExpr]
    | EIf AExpr (Maybe Ty) Expr Expr
    | ERet AExpr
    | EDebug DebugCommand
    | EAssert Prop
    | EAssume Prop
    | EAdmit
    | ECall String ([Idx], [Idx]) [AExpr]
    | ECase AExpr [(String, Either Expr (Ignore String, Bind DataVar Expr))] (Maybe Ty) -- The (Ignore String) part is the name for the var
    | ECorrCase NameExp Expr
    | EFalseElim Expr
    | ETLookup TableName AExpr
    | ETWrite TableName AExpr AExpr
    deriving (Show, Generic, Typeable)

type Expr = Spanned ExprX


data DebugCommand = 
    DebugPrintTyOf AExpr
      | DebugPrint String
      | DebugPrintTy Ty
      | DebugPrintProp Prop
      | DebugPrintTyContext
      | DebugPrintExpr Expr
      | DebugPrintLabel Label
    deriving (Show, Generic, Typeable)

data FuncParam = 
      ParamAExpr AExpr
      | ParamStr String
      | ParamLbl Label
      | ParamTy Ty
      | ParamIdx Idx
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

instance Subst AExpr Endpoint

instance Alpha AExprX
instance Subst Idx AExprX
instance Subst AExpr AExprX where
    isCoerceVar (AEVar _ v) = Just (SubstCoerce v (\x -> Just (_val x)))
    isCoerceVar _ = Nothing

instance Alpha NameExpX
instance Subst Idx NameExpX
instance Subst AExpr NameExpX

instance Alpha NameTypeX
instance Subst Idx NameTypeX
instance Subst AExpr NameTypeX

instance Alpha FuncParam
instance Subst Idx FuncParam
instance Subst AExpr FuncParam

instance Alpha LabelX
instance Subst Idx LabelX
instance Subst AExpr LabelX

instance Alpha TyX
instance Subst Idx TyX
instance Subst AExpr TyX

instance Alpha PropX
instance Subst Idx PropX
instance Subst AExpr PropX


instance Alpha ExprX

instance Alpha DebugCommand

instance Alpha Locality
instance Subst Idx Locality
instance Subst AExpr Locality

--- Pretty instances ---

instance Pretty (Name a) where
    pretty v = pretty $ show v

instance Pretty Idx where
    pretty (IVar _ s) = pretty s

instance Pretty NameExpX where
    pretty (ROName s) = pretty "RO<" <> pretty s <> pretty ">"
    pretty (PRFName n e) = pretty "PRF<" <> pretty n <> pretty ", " <> pretty e <> pretty ">"
    pretty (BaseName vs n) = 
        case vs of
          ([], []) -> pretty n
          (vs1, vs2) -> pretty n <> pretty "<" <> 
              pretty (intercalate "," (map (show . pretty) vs1)) <> 
              pretty "@" <>
              pretty (intercalate "," (map (show . pretty) vs2)) <> 
              pretty ">"

prettyBind :: (Alpha a, Alpha b, Pretty a, Pretty b) => Bind b a -> (Doc ann, Doc ann)
prettyBind b = 
    let (x, y) = unsafeUnbind b in
    (pretty x, pretty y)


instance Pretty LabelX where
    pretty (LName n) = pretty "[" <> pretty n <> pretty "]"
    pretty LZero = pretty "static"
    pretty (LAdv) = pretty "adv"
    pretty (LJoin v1 v2) = pretty v1 <+> pretty "/\\" <+> pretty v2
    pretty (LVar s) = pretty s
    pretty (LRangeIdx l) = 
        let (b, l') = prettyBind l in
        pretty "/\\_" <> b <+> pretty "(" <> l' <> pretty ")"

instance Pretty TyX where
    pretty TUnit =
        pretty "unit"
    pretty (TBool l) = 
            pretty "Bool<" <+> pretty l <> pretty ">"
    pretty (TData l1 l2) = 
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
    pretty (TVar n ps) =
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


instance Pretty PropX where 
    pretty PTrue = pretty "true"
    pretty PFalse = pretty "false"
    pretty (PAnd p1 p2) = pretty p1 <+> pretty "&&" <+> pretty p2
    pretty (POr p1 p2) = pretty p1 <+> pretty "||" <+> pretty p2
    pretty (PNot p) = pretty "!" <+> pretty p
    pretty (PEq e1 e2) = pretty e1 <+> pretty "=" <+> pretty e2
    pretty (PEqIdx e1 e2) = pretty e1 <+> pretty "=idx" <+> pretty e2
    pretty (PImpl p1 p2) = pretty p1 <+> pretty "==>" <+> pretty p2
    pretty (PFlow l1 l2) = pretty l1 <+> pretty "<=" <+> pretty l2
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
    pretty (NT_Enc ty) = pretty "enc" <+> pretty ty
    pretty (NT_PKE ty) = pretty "pke" <+> pretty ty
    pretty (NT_MAC ty) = pretty "mac" <+> pretty ty
    pretty (NT_PRF xs) = pretty "prf" <+> pretty "[" <> mconcat (map (\(ae, nt) -> pretty ae <+> pretty "->" <+> pretty nt) xs) <> pretty "]"
    pretty NT_DH = pretty "DH"
    pretty NT_Nonce = pretty "nonce"


instance Pretty AExprX where
    pretty (AEVar s n) = pretty (unignore s)
    pretty (AEApp f _ as) = pretty f <> tupled (map pretty as)
    pretty (AEString s) = pretty "\"" <> pretty s <> pretty "\""
    pretty (AELenConst s) = pretty "|" <> pretty s <> pretty "|"
    pretty (AEInt i) = pretty i
    pretty (AEGet ne) = pretty "get" <> pretty "(" <> pretty ne <> pretty ")"
    pretty (AEGetEncPK ne) = pretty "get_encpk" <> pretty "(" <> pretty ne <> pretty ")"
    pretty (AEGetVK ne) = pretty "get_vk" <> pretty "(" <> pretty ne <> pretty ")"
    pretty (AEPackIdx s a) = pretty "pack" <> pretty "<" <> pretty s <> pretty ">(" <> pretty a <> pretty ")"

instance Pretty ExprX where 
    pretty (EInput k) = 
        let ((x, i), e) = unsafeUnbind k in
        pretty "input" <+> pretty x <> pretty ", " <> pretty i <> pretty " in " <> pretty e
    pretty (EOutput e l) = pretty "output" <+> pretty e <+> (case l of
       Nothing -> pretty ""
       Just s -> pretty "to" <+> pretty s)
    pretty (ELet e1 tyAnn sx xk) = 
        let (x, k) = prettyBind xk in
        let tann = case tyAnn of
                     Nothing -> mempty
                     Just t -> pretty ":" <+> pretty t
        in
        pretty "let" <+> x <+> tann <+> pretty "=" <+> pretty e1 <+> pretty "in" <+> k
    pretty (EUnionCase a xk) = 
        let (x, k) = prettyBind xk in
        pretty "union_case" <+> x <+> pretty "=" <> pretty a <+>  pretty "in" <+> k
    pretty (EUnpack a k) = pretty "unpack a .... TODO"
    pretty (ESamp d as) = pretty "samp" <+> pretty d <> tupled (map pretty as)
    pretty (EIf t oty e1 e2) = 
        let ann = case oty of
                    Just t' -> pretty "return" <+> pretty t'
                    Nothing -> mempty
        in
        pretty "if" <+> pretty t <+> ann <+> pretty "then" <+> pretty e1 <+> pretty "else" <+> pretty e2
    pretty (ERet ae) = pretty ae
    pretty (EAdmit) = pretty "admit"
    pretty (ECall f is as) = 
        let inds = case is of
                     ([], []) -> mempty
                     (v1, v2) -> pretty "<" <> mconcat (map pretty v1) <> pretty "@" <> mconcat (map pretty v2) <> pretty ">"
        in
        pretty "call" <> inds <+> pretty f <> tupled (map pretty as)
    pretty (ECase t xs oty) = 
        let ann = 
                case oty of
                  Just t -> pretty "return" <+> pretty t
                  Nothing -> mempty
        in
        let pcases = 
                map (\(c, o) -> 
                    case o of
                      Left e -> pretty "|" <+> pretty c <+> pretty "=>" <+> pretty e
                      Right (_, xe) -> let (x, e) = prettyBind xe in pretty "|" <+> pretty c <+> x <+> pretty "=>" <+> e
                    ) xs in
        pretty "case" <+> pretty t <+> ann <+> vsep pcases
    pretty (ECorrCase n e) = 
        pretty "corr_case" <+> pretty n <+> pretty "in" <+> pretty e
    pretty (EDebug dc) = pretty "debug" <+> pretty dc
    pretty (EAssert p) = pretty "assert" <+> pretty p
    pretty (EAssume p) = pretty "assume" <+> pretty p
    pretty (EFalseElim k) = pretty "false_elim in" <+> pretty k
    pretty (ETLookup n a) = pretty "lookup" <> tupled [pretty a]
    pretty (ETWrite n a a') = pretty "write" <> tupled [pretty a, pretty a']

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

instance Pretty Endpoint where
    pretty (Endpoint  x) = pretty x
    pretty (EndpointLocality l) = pretty "endpoint(" <> pretty l <> pretty ")"

instance Pretty Locality where
    pretty (Locality s xs) = pretty s <> angles (mconcat $ map pretty xs)

-- Wrapper datatype for native comparison up to alpha equivalence. Used for
-- indexing maps by ASTs 
newtype AlphaOrd a = AlphaOrd { _unAlphaOrd :: a }

instance Alpha a => Eq (AlphaOrd a) where
    (AlphaOrd x) == (AlphaOrd y) = (x `aeq` y)

instance Alpha a => Ord (AlphaOrd a) where
    compare (AlphaOrd x) (AlphaOrd y) = (x `acompare` y)


tLemma :: Prop -> Ty
tLemma p = tRefined tUnit (bind (s2n "._") p)
