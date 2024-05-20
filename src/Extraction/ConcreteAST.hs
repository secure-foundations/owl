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
    | FBuf (Maybe FLen) -- TODO: maybe we want a data type for built-in length consts, instead of Int
    | FOption FormatTy
    | FStruct String [(String, FormatTy)]           -- name, fields
    | FEnum String [(String, Maybe FormatTy)]  -- name, cases
    deriving (Show, Eq, Generic, Typeable)

data Typed v t = Typed {
    _tty :: t,
    _tval :: v
} deriving (Generic, Typeable)

instance (Show v, Show t) => Show (Typed v t) where
    show (Typed v t) = "(" ++ show t ++ ") : " ++ show v

makeLenses ''Typed

type CDataVar t = Name (CAExpr t)

data CAExpr' t = 
    CAVar (Ignore String) (CDataVar t)
    -- TODO should the type be the variable's type, or the desired type for the func call?
    | CAApp String [CAExpr t] -- args are (expr, type) pairs; 
    | CAGet String
    | CAGetEncPK String
    | CAGetVK String
    | CAInt (FLen)
    | CAHexConst String
    | CACounter String
    deriving (Show, Generic, Typeable)

type CAExpr t = Typed (CAExpr' t) t

data ParseKind = PFromBuf | PFromDatatype
    deriving (Show, Eq, Generic, Typeable)

data CExpr' t = 
    CSkip
    | CRet (CAExpr t)
    | CInput t (Bind (CDataVar t, EndpointVar) (CExpr t)) -- keep track of received buf type
    | COutput (CAExpr t) (Maybe Endpoint)
    | CSample FLen (Bind (CDataVar t) (CExpr t))
    | CLet (CExpr t) (Maybe AExpr) (Bind (CDataVar t) (CExpr t)) -- rhs, ANF annotation, bind (var, cont)
    | CBlock (CExpr t) -- Boundary for scoping; introduced by { }; TODO do we need this?
    | CIf (CAExpr t) (CExpr t) (CExpr t)
    -- Only a regular case statement, not the parsing version
    | CCase (CAExpr t) [(String, Either (CExpr t) (Bind (CDataVar t) (t, CExpr t)))] -- Binding contains type for the bound variable
    | CCall String [CAExpr t]
    -- In concretification, we should compile `ECase` exprs that parse an enum into a 
    -- CParse node containing a regular `CCase`. The list of binds should have one element
    | CParse ParseKind (CAExpr t) t (Maybe (CExpr t)) (Bind [(CDataVar t, Ignore String, t)] (CExpr t))
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
    _defBody :: CDepBind t (t, CExpr t) -- retT, body
} deriving (Show, Generic, Typeable)

makeLenses ''CDef

data CUserFunc t = CUserFunc {
    _ufName :: String,
    _ufBody :: CDepBind t (t, CAExpr t) -- retT, body
} deriving (Show, Generic, Typeable)


data CStruct t = CStruct {
    _structName :: String,
    _structFields :: [(String, t)],
    _structIsVest :: Bool
} deriving (Show, Generic, Typeable)

makeLenses ''CStruct

data CEnum t = CEnum {
    _enumName :: String,
    _enumCases :: M.Map String (Maybe t),
    _enumIsVest :: Bool
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
instance Alpha FormatTy
instance Alpha ParseKind

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
    owlpretty (FLConst i) = owlpretty i
    owlpretty (FLNamed s) = owlpretty s
    owlpretty (FLPlus x y) = owlpretty x <+> owlpretty "+" <+> owlpretty y
    owlpretty (FLCipherlen x) = owlpretty "cipherlen" <> parens (owlpretty x)
    
instance OwlPretty FormatTy where
    owlpretty FUnit = owlpretty "unit"
    owlpretty FBool = owlpretty "bool"
    owlpretty FInt = owlpretty "int"
    owlpretty (FBuf Nothing) = owlpretty "buf[]"
    owlpretty (FBuf (Just l)) = owlpretty "buf" <> brackets (owlpretty l)
    owlpretty (FOption t) = owlpretty "Option" <> parens (owlpretty t)
    owlpretty (FStruct n fs) = owlpretty "struct" <+> owlpretty n 
    owlpretty (FEnum n cs) = owlpretty "enum" <+> owlpretty n 
    owlpretty FGhost = owlpretty "ghost"

flagShouldPrettyTypes :: Bool
flagShouldPrettyTypes = True

instance (OwlPretty v, OwlPretty t) => OwlPretty (Typed v t) where
    owlpretty (Typed v t) = if flagShouldPrettyTypes then parens (owlpretty t) <+> owlpretty ":" <+> owlpretty v else owlpretty t

instance OwlPretty t => OwlPretty (CAExpr' t) where
    owlpretty (CAVar _ v) = owlpretty v
    owlpretty (CAApp f as) = owlpretty f <> tupled (map owlpretty as)
    owlpretty (CAGet n) = owlpretty "get" <> parens (owlpretty n)
    owlpretty (CAInt i) = owlpretty i
    owlpretty (CAHexConst s) = owlpretty "0x" <> owlpretty s
    owlpretty (CACounter s) = owlpretty "counter" <> parens (owlpretty s)


instance OwlPretty ParseKind where
    owlpretty PFromBuf = owlpretty "FromBuf"
    owlpretty PFromDatatype = owlpretty "FromDatatype"

instance (OwlPretty t, Alpha t, Typeable t) => OwlPretty (CExpr' t) where
    owlpretty CSkip = owlpretty "skip"
    owlpretty (CRet a) = owlpretty "ret" <+> owlpretty a
    owlpretty (CInput t xsk) = 
        let (x, sk) = owlprettyBind xsk in
        owlpretty "input" <+> x <> pretty ";" <+> sk
    owlpretty (COutput a l) = owlpretty "output" <+> owlpretty a <+> (case l of
       Nothing -> owlpretty ""
       Just s -> owlpretty "to" <+> owlpretty s)
    owlpretty (CSample n xk) = 
        let (x, k) = owlprettyBind xk in
        owlpretty "sample" <> brackets (owlpretty n) <+> x <+> owlpretty "in" <+> k
    owlpretty (CLet e oanf xk) =
        let (x, k) = owlprettyBind xk in
        owlpretty "let" <> braces (owlpretty oanf) <+> x <+> owlpretty "=" <+> owlpretty e <+> owlpretty "in" <> line <> k
    owlpretty (CBlock e) = owlpretty "{" <+> owlpretty e <+> owlpretty "}"
    owlpretty (CIf a e1 e2) =
        owlpretty "if" <+> owlpretty a <+> owlpretty "then" <+> braces (owlpretty e1) <+> owlpretty "else" <+> braces (owlpretty e2)
    owlpretty (CCase a xs) =
        let pcases =
                map (\(c, o) ->
                    case o of
                      Left e -> owlpretty "|" <+> owlpretty c <+> owlpretty "=>" <+> owlpretty e
                      Right xe -> let (x, e) = owlprettyBind xe in 
                        owlpretty "|" <+> owlpretty c <+> x <+> owlpretty "=>" <+> e
                    ) xs in
        owlpretty "case" <+> owlpretty a <> line <> vsep pcases
    owlpretty (CCall f as) =
        let args = map owlpretty as in
        owlpretty f <> tupled args
    owlpretty (CParse pkind ae t ok bindpat) =
        let (pats', k') = unsafeUnbind bindpat in
        let pats = map (\(n, _, _) -> owlpretty n) pats' in
        let k = owlpretty k' in
        owlpretty "parse" <> brackets (owlpretty pkind) <+> owlpretty ae <+> owlpretty "as" <+> owlpretty t <> tupled pats <+> owlpretty "otherwise" <+> owlpretty ok <+> owlpretty "in" <> line <> k
    owlpretty (CTLookup n a) = owlpretty "lookup" <+> owlpretty n <> brackets (owlpretty a)
    owlpretty (CTWrite n a a') = owlpretty "write" <+> owlpretty n <> brackets (owlpretty a) <+> owlpretty "<-" <+> owlpretty a'
    owlpretty (CGetCtr p) = owlpretty "get_counter" <+> owlpretty p
    owlpretty (CIncCtr p) = owlpretty "inc_counter" <+> owlpretty p


---- traversals ----


traverseTyped :: Applicative f => Typed v t -> (t -> f t2) -> (v -> f v2) -> f (Typed v2 t2)
traverseTyped (Typed t v) ft fv = Typed <$> ft t <*> fv v

castName :: Name a -> Name b
castName (Fn x y) = Fn x y
castName (Bn x y) = Bn x y

-- Does not take into account bound names
traverseCAExpr :: Applicative f => (t -> f t2) -> CAExpr t -> f (CAExpr t2)
traverseCAExpr f a =
    traverseTyped a f $ \c ->
        case c of
          CAVar s n -> pure $ CAVar s $ castName n
          CAApp s xs -> CAApp s <$> traverse (traverseCAExpr f) xs
          CAGet s -> pure $ CAGet s
          CAGetEncPK s -> pure $ CAGetEncPK s
          CAGetVK s -> pure $ CAGetVK s
          CAInt i -> pure $ CAInt i
          CAHexConst i -> pure $ CAHexConst i
          CACounter s -> pure $ CACounter s

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
          CSample n xk -> do
                (x, k) <- unbind xk
                CSample n . bind (castName x) <$> traverseCExpr f k
          CLet e a bk -> do
              (n, k) <- unbind bk
              CLet <$> traverseCExpr f e <*> pure a <*> (bind (castName n) <$> traverseCExpr f k)
          CBlock e -> CBlock <$> traverseCExpr f e
          CIf x y z -> CIf <$> traverseCAExpr f x <*> traverseCExpr f y <*> traverseCExpr f z
          CCall s xs -> CCall <$> pure s <*> traverse (traverseCAExpr f) xs
          CGetCtr s -> pure $ CGetCtr s
          CIncCtr s -> pure $ CIncCtr s
          CParse pkind x y z bw -> do
              (xts, w) <- unbind bw
              xts' <- mapM (\(n, s, t) -> do t' <- f t ; return (castName n, s, t')) xts
              w' <- traverseCExpr f w
              CParse pkind <$> traverseCAExpr f x <*> f y <*> traverse (traverseCExpr f) z <*> 
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
        let (x, sk) = owlprettyBind xsk in
        owlpretty "input" <+> x <> pretty ";" <+> sk
    owlpretty (COutput a l) = owlpretty "output " <> owlpretty a <+> (case l of
       Nothing -> owlpretty ""
       Just s -> owlpretty "to" <+> owlpretty s)
    owlpretty (CLet e oanf xk) =
        let (x, k) = owlprettyBind xk in
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
                      Right xe -> let (x, e) = owlprettyBind xe in owlpretty "|" <+> owlpretty c <+> x <+> owlpretty "=>" <+> e
                    ) xs in
        owlpretty "case" <+> owlpretty a <> line <> vsep pcases
    owlpretty (CTLookup n a) = owlpretty "lookup" <> tupled [owlpretty a]
    owlpretty (CTWrite n a a') = owlpretty "write" <> tupled [owlpretty a, owlpretty a']
    owlpretty (CIncCtr p idxs) = owlpretty "inc_counter" <> angles (owlpretty idxs) <> parens (owlpretty p)
    owlpretty (CGetCtr p idxs) = owlpretty "get_counter" <> angles (owlpretty idxs) <> parens (owlpretty p)
    owlpretty (CParse ae t ok bindpat) = 
        let (pats, k) = owlprettyBind bindpat in
        owlpretty "parse" <+> owlpretty ae <+> owlpretty "as" <+> owlpretty t <> parens pats <+> owlpretty "otherwise" <+> owlpretty ok <+> owlpretty "in" <> line <> k


-}
