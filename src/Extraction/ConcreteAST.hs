{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
module ConcreteAST where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Control.Monad
import Control.Lens
import Prettyprinter
import Pretty
import Data.Type.Equality
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Unsafe
import Unbound.Generics.LocallyNameless.TH
import Unbound.Generics.LocallyNameless.Name ( Name(Bn, Fn) )
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import ANFPass (isGhostTyAnn)
import AST
import Verus
import qualified TypingBase as TB


data BufSecrecy = BufSecret | BufPublic
    deriving (Show, Eq, Generic, Typeable)

data FLen = 
    FLConst Int
    | FLNamed String
    | FLPlus FLen FLen
    | FLCipherlen FLen
    deriving (Show, Eq, Generic, Typeable)

data FormatTy =
    FUnit
    | FBool
    | FGhost  -- For erased variables
    | FInt
    | FBuf BufSecrecy (Maybe FLen) 
    | FOption FormatTy
    | FStruct String [(String, FormatTy)]           -- name, fields
    | FEnum String [(String, Maybe FormatTy)]  -- name, cases
    | FHexConst String
    | FDummy -- for when we can't infer the type locally
    | FDeclassifyTok
    deriving (Show, Eq, Generic, Typeable)

data Typed v t = Typed {
    _tty :: t,
    _tval :: v
} deriving (Generic, Typeable)

instance (Show v, Show t) => Show (Typed v t) where
    show (Typed v t) = "(" ++ show t ++ ") : " ++ show v

makeLenses ''Typed

data ParsleyCombinator =
    PCConstBytes Int String
    | PCBytes FLen
    | PCTail
    | PCBuilder
    deriving (Show, Eq, Generic, Typeable)


type CDataVar t = Name (CAExpr t)

data CAExpr' t = 
    CAVar (Ignore String) (CDataVar t)
    -- first String is the function name in exec, second String is the function name in spec, args are (expr, type) pairs; 
    | CAApp String String [CAExpr t] 
    | CAGet String
    | CAGetEncPK String
    | CAGetVK String
    | CAInt FLen
    | CAHexConst String
    | CACounter String
    | CASerializeWith t [(CAExpr t, ParsleyCombinator)]
    | CACast (CAExpr t) t -- (source expr, target type)
    deriving (Show, Generic, Typeable)

type CAExpr t = Typed (CAExpr' t) t

data DeclassifyingOp t = 
    DOControlFlow (CAExpr t)
    | DOEnumParse (CAExpr t)
    | DOEqCheck (CAExpr t, CAExpr t)  
    | DOADec (CAExpr t, CAExpr t)
    | DOStAeadDec (CAExpr t, CAExpr t, CAExpr t, CAExpr t)
    | DOSigVrfy (CAExpr t, CAExpr t, CAExpr t)
    | DOMacVrfy (CAExpr t, CAExpr t, CAExpr t)
    | DOPkDec (CAExpr t, CAExpr t)
    deriving (Show, Generic, Typeable)

data ParseKind = PFromBuf | PFromDatatype | PFromSecBuf
    deriving (Show, Eq, Generic, Typeable)

data CExpr' t = 
    CSkip
    | CRet (CAExpr t)
    | CInput t (Bind (CDataVar t, EndpointVar) (CExpr t)) -- keep track of received buf type
    | COutput (CAExpr t) (Maybe Endpoint)
    | CSample FLen t (Bind (CDataVar t) (CExpr t))
    | CItreeDeclassify (DeclassifyingOp t) (Bind (CDataVar t) (CExpr t))
    | CLet (CExpr t) (Maybe AExpr) (Bind (CDataVar t) (CExpr t)) -- rhs, ANF annotation, bind (var, cont)
    | CBlock (CExpr t) -- Boundary for scoping; introduced by { }; TODO do we need this?
    | CIf (CAExpr t) (CExpr t) (CExpr t)
    -- Only a regular case statement, not the parsing version
    | CCase (CAExpr t) [(String, Either (CExpr t) (Bind (CDataVar t) (t, CExpr t)))] -- Binding contains type for the bound variable
    -- Include the return type of the call
    | CCall String t [CAExpr t]
    -- In concretification, we should compile `ECase` exprs that parse an enum into a 
    -- CParse node containing a regular `CCase`. The list of binds should have one element
    -- Extra [CAExpr t] is for extra arguments to the parsing function
    | CParse ParseKind (CAExpr t) [CAExpr t] t (Maybe (CExpr t)) (Bind [(CDataVar t, Ignore String, t)] (CExpr t))
    | CTLookup String (CAExpr t)
    | CTWrite String (CAExpr t) (CAExpr t)
    -- Crypto calls should be compiled to `CRet (CAApp ...)` during concretization
    -- | CCrypt CryptOp [AExpr]
    | CGetCtr String 
    | CIncCtr String 
    deriving (Show, Generic, Typeable)    

type CExpr t = Typed (CExpr' t) t

data CDepBind t a = CDPDone a | CDPVar t String (Bind (CDataVar t) (CDepBind t a))
    deriving (Show, Generic, Typeable)

data CDef t = CDef {
    _defName :: String,
    _defBody :: CDepBind t (t, Maybe (CExpr t)) -- retT, body
} deriving (Show, Generic, Typeable)

makeLenses ''CDef

data CUserFunc t = CUserFunc {
    _ufSpecName :: String,
    _ufPubName :: String,
    _ufSecName :: String,
    _ufPubBody :: CDepBind t (t, CAExpr t), -- retT, body
    _ufSecBody :: CDepBind t (t, CAExpr t) -- retT, body
} deriving (Show, Generic, Typeable)

makeLenses ''CUserFunc

data CStruct t = CStruct {
    _structName :: String,
    _structFields :: [(String, t)],
    _structIsVest :: Bool,
    _structHasSecretParse :: Bool,
    _structHasSecretSer :: Bool
} deriving (Show, Generic, Typeable)

makeLenses ''CStruct

data CEnum t = CEnum {
    _enumName :: String,
    _enumCases :: M.Map String (Maybe t),
    _enumIsVest :: Bool,
    _enumExecComb :: String,
    _enumIsSecret :: Bool
} deriving (Show, Generic, Typeable)

makeLenses ''CEnum

data CTyDef t =
    CStructDef (CStruct t)
    | CEnumDef (CEnum t)
    deriving (Show, Generic, Typeable)


--------------------------------------------------------------------------------
-- LocallyNameless

-- TODO: check these
--

instance Alpha FLen
instance Alpha BufSecrecy
instance Alpha FormatTy
instance Alpha ParseKind
instance Alpha ParsleyCombinator
instance (Typeable t, Alpha t) => Alpha (DeclassifyingOp t)

instance (Alpha v, Alpha t) => Alpha (Typed v t)
instance (Subst b a, Subst b t) => Subst b (Typed a t)

instance (Alpha t, Typeable t) => Alpha (CAExpr' t)
instance (Alpha t, Typeable t) => Alpha (CExpr' t)

instance (Typeable t, Alpha a, Alpha t) => Alpha (CDepBind t a)
instance (Typeable t, Alpha a, Alpha t, Subst b a, Subst b t) => Subst b (CDepBind t a)


--------------------------------------------------------------------------------
-- Helper funcs


--------------------------------------------------------------------------------
-- Pretty

instance OwlPretty FLen where
    owlpretty' _ (FLConst i) = owlpretty i
    owlpretty' _ (FLNamed s) = owlpretty s
    owlpretty' _ (FLPlus x y) = owlpretty x <+> owlpretty "+" <+> owlpretty y
    owlpretty' _ (FLCipherlen x) = owlpretty "cipherlen" <> parens (owlpretty x)
    
instance OwlPretty FormatTy where
    owlpretty' _ FUnit = owlpretty "unit"
    owlpretty' _ FBool = owlpretty "bool"
    owlpretty' _ FInt = owlpretty "int"
    owlpretty' _ (FBuf BufPublic Nothing) = owlpretty "buf[]"
    owlpretty' _ (FBuf BufPublic (Just l)) = owlpretty "buf" <> brackets (owlpretty l)
    owlpretty' _ (FBuf BufSecret Nothing) = owlpretty "secbuf[]"
    owlpretty' _ (FBuf BufSecret (Just l)) = owlpretty "secbuf" <> brackets (owlpretty l)
    owlpretty' _ (FOption t) = owlpretty "Option" <> parens (owlpretty t)
    owlpretty' _ (FStruct n fs) = owlpretty "struct" <+> owlpretty n 
    owlpretty' _ (FEnum n cs) = owlpretty "enum" <+> owlpretty n 
    owlpretty' _ FGhost = owlpretty "ghost"
    owlpretty' _ FDummy = owlpretty "dummy"
    owlpretty' _ (FHexConst s) = owlpretty "HexConst" <> parens (owlpretty "0x" <> owlpretty s)
    owlpretty' _ FDeclassifyTok = owlpretty "DeclassifyingOpToken"

flagShouldPrettyTypes :: Bool
flagShouldPrettyTypes = True

instance (OwlPretty v, OwlPretty t) => OwlPretty (Typed v t) where
    owlpretty' b (Typed v t) = if flagShouldPrettyTypes then parens (owlpretty' b t) <+> owlpretty ":" <+> owlpretty' b v else owlpretty' b t

instance OwlPretty ParsleyCombinator where
    owlpretty' _ (PCConstBytes n s) = owlpretty "Tag<BytesN" <> angles (owlpretty n) <> owlpretty ", [u8; " <> owlpretty n <> owlpretty "]" <> parens (owlpretty s)
    owlpretty' _ (PCBytes l) = owlpretty "Bytes" <> parens (owlpretty l)
    owlpretty' _ PCTail = owlpretty "Tail"
    owlpretty' _ PCBuilder = owlpretty "BuilderCombinator"

instance OwlPretty t => OwlPretty (DeclassifyingOp t) where
    owlpretty' _ (DOControlFlow e) = owlpretty "ControlFlow" <> parens (owlpretty e)
    owlpretty' _ (DOEnumParse e) = owlpretty "EnumParse" <> parens (owlpretty e)
    owlpretty' _ (DOEqCheck (a, b)) = owlpretty "EqCheck" <> parens (owlpretty a <> comma <+> owlpretty b)
    owlpretty' _ (DOADec (a, b)) = owlpretty "ADec" <> parens (owlpretty a <> comma <+> owlpretty b)
    owlpretty' _ (DOStAeadDec (a, b, c, d)) = owlpretty "StAeadDec" <> parens (owlpretty a <> comma <+> owlpretty b <> comma <+> owlpretty c <> comma <+> owlpretty d)
    owlpretty' _ (DOSigVrfy (a, b, c)) = owlpretty "SigVrfy" <> parens (owlpretty a <> comma <+> owlpretty b <> comma <+> owlpretty c)
    owlpretty' _ (DOMacVrfy (a, b, c)) = owlpretty "MacVrfy" <> parens (owlpretty a <> comma <+> owlpretty b <> comma <+> owlpretty c)
    owlpretty' _ (DOPkDec (a, b)) = owlpretty "PkDec" <> parens (owlpretty a <> comma <+> owlpretty b)

instance OwlPretty t => OwlPretty (CAExpr' t) where
    owlpretty' _ (CAVar _ v) = owlpretty v
    owlpretty' _ (CAApp f spec_f as) = owlpretty f <> brackets (owlpretty spec_f) <> tupled (map owlpretty as)
    owlpretty' _ (CAGet n) = owlpretty "get" <> parens (owlpretty n)
    owlpretty' _ (CAInt i) = owlpretty i
    owlpretty' _ (CAHexConst s) = owlpretty "0x" <> owlpretty s
    owlpretty' _ (CACounter s) = owlpretty "counter" <> parens (owlpretty s)
    owlpretty' _ (CASerializeWith t xs) = 
        let xs' = map (\(e, p) -> owlpretty e <+> owlpretty "as" <+> owlpretty p) xs in
        owlpretty "serialize" <> brackets (owlpretty t) <+> owlpretty "(" <> line <> vsep xs' <> owlpretty ")"
    owlpretty' _ (CAGetEncPK s) = owlpretty "get_enc_pk" <> parens (owlpretty s)
    owlpretty' _ (CAGetVK s) = owlpretty "get_vk" <> parens (owlpretty s)
    owlpretty' _ (CACast e t) = parens $ owlpretty "cast" <+> owlpretty e <+> owlpretty "as" <+> owlpretty t


instance OwlPretty ParseKind where
    owlpretty' _ PFromBuf = owlpretty "FromBuf"
    owlpretty' _ PFromDatatype = owlpretty "FromDatatype"
    owlpretty' _ PFromSecBuf = owlpretty "FromSecBuf"

instance (OwlPretty t, Alpha t, Typeable t) => OwlPretty (CExpr' t) where
    owlpretty' _ CSkip = owlpretty "skip"
    owlpretty' _ (CRet a) = owlpretty "ret" <+> owlpretty a
    owlpretty' _ (CInput t xsk) = 
        let (x, sk) = owlprettyBind xsk in
        owlpretty "input" <+> x <> pretty ";" <+> sk
    owlpretty' _ (COutput a l) = owlpretty "output" <+> owlpretty a <+> (case l of
       Nothing -> owlpretty ""
       Just s -> owlpretty "to" <+> owlpretty s)
    owlpretty' _ (CSample n t xk) = 
        let (x, k) = owlprettyBind xk in
        owlpretty "sample" <> brackets (owlpretty n) <+> x <+> owlpretty "in" <+> k
    owlpretty' _ (CItreeDeclassify dop xk) = 
        let (x, k) = owlprettyBind xk in
        owlpretty "let" <+> x <+> owlpretty "=" <+> owlpretty "itree_declassify" <> parens (owlpretty dop) <+> owlpretty "in" <+> k
    owlpretty' _ (CLet e oanf xk) =
        let (x, k) = owlprettyBind xk in
        owlpretty "let" <> braces (owlpretty oanf) <+> x <+> owlpretty "=" <+> owlpretty e <+> owlpretty "in" <> line <> k
    owlpretty' _ (CBlock e) = owlpretty "{" <+> owlpretty e <+> owlpretty "}"
    owlpretty' _ (CIf a e1 e2) =
        owlpretty "if" <+> owlpretty a <+> owlpretty "then" <+> braces (owlpretty e1) <+> owlpretty "else" <+> braces (owlpretty e2)
    owlpretty' _ (CCase a xs) =
        let pcases =
                map (\(c, o) ->
                    case o of
                      Left e -> owlpretty "|" <+> owlpretty c <+> owlpretty "=>" <+> owlpretty e
                      Right xe -> let (x, e) = owlprettyBind xe in 
                        owlpretty "|" <+> owlpretty c <+> x <+> owlpretty "=>" <+> e
                    ) xs in
        owlpretty "case" <+> owlpretty a <> line <> vsep pcases
    owlpretty' _ (CCall f rty as) =
        let args = map owlpretty as in
        owlpretty f <> tupled args <+> owlpretty ":" <+> owlpretty rty
    owlpretty' _ (CParse pkind ae extraArgs t ok bindpat) =
        let (pats', k') = unsafeUnbind bindpat in
        let pats = map (\(n, _, _) -> owlpretty n) pats' in
        let k = owlpretty k' in
        owlpretty "parse" <> brackets (owlpretty pkind) <+> owlpretty ae <+> parens (owlpretty extraArgs) <+> owlpretty "as" <+> owlpretty t <> tupled pats <+> owlpretty "otherwise" <+> owlpretty ok <+> owlpretty "in" <> line <> k
    owlpretty' _ (CTLookup n a) = owlpretty "lookup" <+> owlpretty n <> brackets (owlpretty a)
    owlpretty' _ (CTWrite n a a') = owlpretty "write" <+> owlpretty n <> brackets (owlpretty a) <+> owlpretty "<-" <+> owlpretty a'
    owlpretty' _ (CGetCtr p) = owlpretty "get_counter" <+> owlpretty p
    owlpretty' _ (CIncCtr p) = owlpretty "inc_counter" <+> owlpretty p


---- traversals ----


traverseTyped :: Applicative f => Typed v t -> (t -> f t2) -> (v -> f v2) -> f (Typed v2 t2)
traverseTyped (Typed t v) ft fv = Typed <$> ft t <*> fv v

castName :: Name a -> Name b
castName (Fn x y) = Fn x y
castName (Bn x y) = Bn x y

traverseDeclassifyingOp :: Applicative f => (t -> f t2) -> DeclassifyingOp t -> f (DeclassifyingOp t2)
traverseDeclassifyingOp f dop =
    case dop of
        DOControlFlow e -> DOControlFlow <$> traverseCAExpr f e
        DOEnumParse e -> DOEnumParse <$> traverseCAExpr f e
        DOEqCheck (a, b) -> DOEqCheck <$> ((,) <$> traverseCAExpr f a <*> traverseCAExpr f b)
        DOADec (a, b) -> DOADec <$> ((,) <$> traverseCAExpr f a <*> traverseCAExpr f b)
        DOStAeadDec (a, b, c, d) -> DOStAeadDec <$> ((,,,) <$> traverseCAExpr f a <*> traverseCAExpr f b <*> traverseCAExpr f c <*> traverseCAExpr f d)
        DOSigVrfy (a, b, c) -> DOSigVrfy <$> ((,,) <$> traverseCAExpr f a <*> traverseCAExpr f b <*> traverseCAExpr f c)
        DOMacVrfy (a, b, c) -> DOMacVrfy <$> ((,,) <$> traverseCAExpr f a <*> traverseCAExpr f b <*> traverseCAExpr f c)
        DOPkDec (a, b) -> DOPkDec <$> ((,) <$> traverseCAExpr f a <*> traverseCAExpr f b)


-- Does not take into account bound names
traverseCAExpr :: Applicative f => (t -> f t2) -> CAExpr t -> f (CAExpr t2)
traverseCAExpr f a =
    traverseTyped a f $ \c ->
        case c of
          CAVar s n -> pure $ CAVar s $ castName n
          CAApp s s' xs -> CAApp s s' <$> traverse (traverseCAExpr f) xs
          CAGet s -> pure $ CAGet s
          CAGetEncPK s -> pure $ CAGetEncPK s
          CAGetVK s -> pure $ CAGetVK s
          CAInt i -> pure $ CAInt i
          CAHexConst i -> pure $ CAHexConst i
          CACounter s -> pure $ CACounter s
          CASerializeWith t xs -> CASerializeWith <$> f t <*> traverse (\(e, p) -> (,) <$> traverseCAExpr f e <*> pure p) xs
          CACast e t -> CACast <$> traverseCAExpr f e <*> f t

-- Does not take into account bound names
traverseCExpr :: (Fresh f, Applicative f, Alpha t, Alpha t2, Typeable t, Typeable t2) => (t -> f t2) -> CExpr t -> f (CExpr t2)
traverseCExpr f a =
    traverseTyped a f $ \c ->
        case c of
          CSkip -> pure CSkip
          CInput t bk -> do
              ((n, ep), k) <- unbind bk                         
              t' <- f t
              CInput t' . bind (castName n, ep) <$> traverseCExpr f k
          COutput e k -> COutput <$> traverseCAExpr f e <*> pure k
          CSample n t xk -> do
                (x, k) <- unbind xk
                t' <- f t
                CSample n t' . bind (castName x) <$> traverseCExpr f k
          CItreeDeclassify dop xk -> do
              (x, k) <- unbind xk
              dop' <- traverseDeclassifyingOp f dop
              CItreeDeclassify dop' . bind (castName x) <$> traverseCExpr f k
          CLet e a bk -> do
              (n, k) <- unbind bk
              CLet <$> traverseCExpr f e <*> pure a <*> (bind (castName n) <$> traverseCExpr f k)
          CBlock e -> CBlock <$> traverseCExpr f e
          CIf x y z -> CIf <$> traverseCAExpr f x <*> traverseCExpr f y <*> traverseCExpr f z
          CCall s t xs -> CCall <$> pure s <*> f t <*> traverse (traverseCAExpr f) xs
          CGetCtr s -> pure $ CGetCtr s
          CIncCtr s -> pure $ CIncCtr s
          CParse pkind x xs y z bw -> do
              (xts, w) <- unbind bw
              xts' <- mapM (\(n, s, t) -> do t' <- f t ; return (castName n, s, t')) xts
              w' <- traverseCExpr f w
              x' <- traverseCAExpr f x
              CParse pkind <$> traverseCAExpr f x <*> traverse (traverseCAExpr f) xs <*> f y <*> traverse (traverseCExpr f) z <*> 
                  pure (bind xts' w')
          CTLookup s a -> CTLookup <$> pure s <*> traverseCAExpr f a
          CTWrite s a b -> CTWrite <$> pure s <*> traverseCAExpr f a <*> traverseCAExpr f b
          CCase x zs -> do
              zs' <- traverse (\(s, e) ->
                  case e of
                    Left a -> do
                        a' <- traverseCExpr f a
                        pure (s, Left a')
                    Right b -> do
                        (n, (t, e)) <- unbind b
                        t2 <- f t
                        e' <- traverseCExpr f e
                        pure (s, Right $ bind (castName n) (t2, e'))) zs
              CCase <$> traverseCAExpr f x <*> pure zs'
          CRet e -> CRet <$> traverseCAExpr f e

--------------------------------------------------------------------------------
-- ConcreteAST utils

fPBuf :: Maybe FLen -> FormatTy
fPBuf = FBuf BufPublic

fSBuf :: Maybe FLen -> FormatTy
fSBuf = FBuf BufSecret



{- 
--------------------------------------------------------------------------------

data CTy =
    CTData
    | CTDataWithLength AExpr
    | CTOption CTy
    | CTGhost
    | CTConst (Path)
    | CTBool
    -- | CTUnion CTy CTy
    | CTUnit
    | CTName NameExp -- Singleton type
    | CTVK NameExp -- Singleton type
    | CTDH_PK NameExp -- Singleton type
    | CTEnc_PK NameExp -- Singleton type
    | CTSS NameExp NameExp -- Singleton type
    | CTHex String -- hex constant string
    deriving (Show, Generic, Typeable)

instance Alpha CTy
instance Subst AExpr CTy

-- data CExpr =
--     CSkip
--     | CInput (Bind (DataVar, EndpointVar) CExpr)
--     | COutput AExpr (Maybe Endpoint)
--     | CLet CExpr (Maybe AExpr) (Bind DataVar CExpr)
--     | CLetGhost (Bind DataVar CExpr)
--     | CBlock CExpr -- Boundary for scoping; introduced by { }
--     | CIf AExpr CExpr CExpr
--     | CRet AExpr
--     | CCall Path ([Idx], [Idx]) [AExpr]
--     | CParse AExpr CTy (Maybe CExpr) (Bind [(DataVar, Ignore String)] CExpr)
--     | CCase AExpr (Maybe (CTy, CExpr)) [(String, Either CExpr (Bind DataVar CExpr))]
--     | CTLookup Path AExpr
--     | CTWrite Path AExpr AExpr
--     | CCrypt CryptOp [AExpr]
--     | CGetCtr Path ([Idx], [Idx])
--     | CIncCtr Path ([Idx], [Idx])
--     deriving (Show, Generic, Typeable)

instance Alpha (CExpr t)
instance Subst AExpr (CExpr t)


compatTys :: CTy -> CTy -> Bool
compatTys (CTName n1) (CTName n2) =
    case (n1 ^. val, n2 ^. val) of
        (KDFName _ _ _ nks1 i1 _ _, KDFName _ _ _ nks2 i2 _ _) ->
            (nks1 !! i1) `aeq` (nks2 !! i2)
        _ -> n1 `aeq` n2
compatTys (CTDH_PK _) (CTDH_PK _) = True
compatTys ct1 ct2 = ct1 `aeq` ct2

-- For struct compilation, not general
concretifyTy :: Fresh m => Ty -> m CTy
concretifyTy t =
  case t^.val of
    TData _ _ _ -> return CTData
    TGhost -> return CTGhost
    TDataWithLength _ l -> return $ CTDataWithLength l
    TRefined t _ _ -> concretifyTy t
    TOption t -> do
      ct <- concretifyTy t
      return $ CTOption ct
    TCase _ t t' -> do
      ct <- concretifyTy t
      ct' <- concretifyTy t'
      case (ct, ct') of
        (cct, CTData) -> return cct
        (CTData, cct') -> return cct'
        _ -> if ct `compatTys` ct' then return ct else 
            error $ "concretifyTy on TCase failed: " ++ show (owlpretty ct) ++ ", " ++ show (owlpretty ct')
    TConst s _ -> return $ CTConst s
    TBool _ -> return CTBool
    TUnit -> return CTUnit
    TName n -> return $ CTName n
    TVK n -> return $ CTVK n
    TDH_PK n -> return $ CTDH_PK n
    TEnc_PK n -> return $ CTEnc_PK n
    TSS n n' -> return $ CTSS n n'
    TAdmit -> error "concretifyTy on TAdmit"
    TExistsIdx _ it -> do
      (_, t) <- unbind it
      concretifyTy t
    THexConst a -> return $ CTHex a

doConcretifyTy :: Ty -> CTy
doConcretifyTy = runFreshM . concretifyTy



concretify :: Fresh m => Expr -> m (CExpr t)
concretify e =
    case e^.val of
        EInput _ xse -> do
            let (xe, e) = unsafeUnbind xse
            c <- concretify e
            return $ CInput $ bind xe c
        EOutput a eo -> return $ COutput a eo
        ELet e1 tyann oanf _ xk | isGhostTyAnn tyann -> do
            let (x, k) = unsafeUnbind xk   
            k' <- concretify k
            return $ CLetGhost (bind x k')
        ELet e1 tyann oanf _ xk -> do
            e1' <- concretify e1
            let (x, k) = unsafeUnbind xk
            k' <- concretify k
            case e1' of
                CSkip -> return k'
                _ -> return $ CLet e1' oanf (bind x k')
        EBlock e _ -> do
            c <- concretify e
            return $ CBlock c
        EUnpack a _ ixk -> do
            ((i, x), k) <- unbind ixk
            k' <- concretify k
            return $ subst x a k' -- i is dangling here, but that shouldn't matter
        EChooseIdx _ _ ixk -> do
            (i, k) <- unbind ixk
            k' <- concretify k
            return k' -- i is free here; irrelevant
        EChooseBV _ _ xk -> do
            (x, k) <- unbind xk
            concretify k -- x is ghost, irrelevant. TODO: make a unit?
        EIf a e1 e2 -> do
            c1 <- concretify e1
            c2 <- concretify e2
            return $ CIf a c1 c2
        EGuard ae e -> do
            -- The aexpr must have type bool, and the expr must have type Option<_>
            -- During concretization we desugar into an if statement
            c <- concretify e
            -- During typechecking the option needs to carry around its type, but during 
            -- extraction this is not required, so we just leave it blank
            return $ CIf ae c (CRet (mkSpanned (AEApp (topLevelPath "None") [] [])))
        ERet a -> return $ CRet a
        EDebug _ -> return CSkip 
        EAssert _ -> return CSkip
        EAssume _ -> return CSkip -- error "Concretify on assume"
        EAdmit -> error "Concretify on admit"
        EForallBV _ _ -> return CSkip
        EForallIdx _ _ -> return CSkip
        ECall a b c -> return $ CCall a b c
        EParse ae t ok bindpat -> do
            let (pats, k) = unsafeUnbind bindpat
            k' <- concretify k
            ok' <- traverse concretify ok
            t' <- concretifyTy t
            return $ CParse ae t' ok' (bind pats k')
        ECase a otk cases -> do 
            a' <- concretify a
            cases' <- forM cases $ \(c, o) ->
                case o of
                    Left e -> do
                        e' <- concretify e
                        return (c, Left e')
                    Right (_, xk) -> do
                        let (x, k) = unsafeUnbind xk
                        k' <- concretify k
                        return (c, Right $ bind x k')
            avar <- fresh $ s2n "caseval"
            otk' <- case otk of
                Nothing -> return Nothing
                Just (t,k) -> do
                    t' <- concretifyTy t
                    k' <- concretify k
                    return $ Just (t', k')
            return $ CLet a' Nothing (bind avar $ CCase (mkSpanned $ AEVar (ignore $ show avar) avar) otk' cases')
        EPCase _ _ _ k -> concretify k
        EPackIdx _ k -> concretify k
        EFalseElim e _ -> concretify e
        ETLookup n a -> return $ CTLookup n a
        ETWrite n a a2 -> return $ CTWrite n a a2
        ECrypt (CLemma _) _ -> return CSkip -- lemma calls are ghost
        ECrypt op args -> return $ CCrypt op args
        EIncCtr p idxs -> return $ CIncCtr p idxs
        EGetCtr p idxs -> return $ CGetCtr p idxs
        ESetOption _ _ e -> concretify e
        ELetGhost _ _ xk -> do
            -- TODO check this
            let (x, k) = unsafeUnbind xk
            k' <- concretify k
            return $ CLetGhost (bind x k')
        ECorrCaseNameOf _ _ k -> concretify k
        -- _ -> error $ "Concretify on " ++ show (owlpretty e)

doConcretify :: Expr -> (CExpr t)
doConcretify = runFreshM . concretify

instance OwlPretty CTy where
    owlpretty CTData = owlpretty "Data"
    owlpretty CTUnit =
        owlpretty "unit"
    owlpretty CTBool =
            owlpretty "Bool"
    owlpretty (CTDataWithLength a) =
            owlpretty "Data " <+> owlpretty "|" <> owlpretty a <> owlpretty "|"
    owlpretty (CTOption t) =
            owlpretty "Option" <> owlpretty t
    owlpretty (CTConst n) =
            owlpretty n
    owlpretty (CTName n) =
            owlpretty "Name(" <> owlpretty n <> owlpretty ")"
    owlpretty (CTVK n) =
            owlpretty "vk(" <> owlpretty n <> owlpretty ")"
    owlpretty (CTDH_PK n) =
            owlpretty "dhpk(" <> owlpretty n <> owlpretty ")"
    owlpretty (CTEnc_PK n) =
            owlpretty "encpk(" <> owlpretty n <> owlpretty ")"
    owlpretty (CTSS n m) =
            owlpretty "shared_secret(" <> owlpretty n <> owlpretty ", " <> owlpretty m <> owlpretty ")"
    owlpretty (CTHex a) =
            owlpretty "Const(" <> owlpretty "0x" <> owlpretty a <> owlpretty ")"
    owlpretty CTGhost = 
            owlpretty "Ghost"
    -- owlpretty (CTUnion t1 t2) =
    --     owlpretty "Union<" <> owlpretty t1 <> owlpretty "," <> owlpretty t2 <> owlpretty ">"

instance OwlPretty (CExpr t) where
    owlpretty CSkip = owlpretty "skip"
    owlpretty (CInput xsk) = 
        let (x, sk) = owlprettyBind' xsk in
        owlpretty "input" <+> x <> pretty ";" <+> sk
    owlpretty (COutput a l) = owlpretty "output " <> owlpretty a <+> (case l of
       Nothing -> owlpretty ""
       Just s -> owlpretty "to" <+> owlpretty s)
    owlpretty (CLet e oanf xk) =
        let (x, k) = owlprettyBind' xk in
        owlpretty "let" <> braces (owlpretty oanf) <+> x <+> owlpretty "=" <+> owlpretty e <+> owlpretty "in" <> line <> k
    owlpretty (CBlock e) = owlpretty "{" <+> owlpretty e <+> owlpretty "}"
    owlpretty (CIf a e1 e2) =
        owlpretty "if" <+> owlpretty a <+> owlpretty "then" <+> owlpretty e1 <+> owlpretty "else" <+> owlpretty e2
    owlpretty (CRet a) = owlpretty "ret " <> owlpretty a
    owlpretty (CCall f is as) = 
        let inds = case is of
                     ([], []) -> mempty
                     (v1, v2) -> owlpretty "<" <> mconcat (map owlpretty v1) <> owlpretty "@" <> mconcat (map owlpretty v2) <> owlpretty ">"
        in
        owlpretty f <> inds <> tupled (map owlpretty as)
    owlpretty (CCase a otk xs) =
        let pcases =
                map (\(c, o) ->
                    case o of
                      Left e -> owlpretty "|" <+> owlpretty c <+> owlpretty "=>" <+> owlpretty e
                      Right xe -> let (x, e) = owlprettyBind' xe in owlpretty "|" <+> owlpretty c <+> x <+> owlpretty "=>" <+> e
                    ) xs in
        owlpretty "case" <+> owlpretty a <> line <> vsep pcases
    owlpretty (CTLookup n a) = owlpretty "lookup" <> tupled [owlpretty a]
    owlpretty (CTWrite n a a') = owlpretty "write" <> tupled [owlpretty a, owlpretty a']
    owlpretty (CIncCtr p idxs) = owlpretty "inc_counter" <> angles (owlpretty idxs) <> parens (owlpretty p)
    owlpretty (CGetCtr p idxs) = owlpretty "get_counter" <> angles (owlpretty idxs) <> parens (owlpretty p)
    owlpretty (CParse ae t ok bindpat) = 
        let (pats, k) = owlprettyBind' bindpat in
        owlpretty "parse" <+> owlpretty ae <+> owlpretty "as" <+> owlpretty t <> parens pats <+> owlpretty "otherwise" <+> owlpretty ok <+> owlpretty "in" <> line <> k


-}
