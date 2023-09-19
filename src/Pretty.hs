{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Pretty where
import AST
import Prettyprinter
import Error.Diagnose
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Unsafe
import Prettyprinter.Render.Terminal
import Data.List

type OwlDoc = Doc AnsiStyle

class OwlPretty a where
    owlpretty :: a -> Doc AnsiStyle

instance OwlPretty Char where
    owlpretty = pretty

instance OwlPretty a => OwlPretty (Ignore a) where
    owlpretty x = owlpretty (unignore x)

instance OwlPretty Bool where
    owlpretty = pretty

instance OwlPretty Int where
    owlpretty = pretty

instance OwlPretty a => OwlPretty [a] where
    owlpretty = mconcat . map owlpretty

instance OwlPretty a => OwlPretty (Maybe a) where
    owlpretty Nothing = mempty
    owlpretty (Just x) = owlpretty x

instance OwlPretty a => OwlPretty (Spanned a) where
    owlpretty (Spanned _ v) = owlpretty v

instance OwlPretty Position where
    owlpretty = pretty

instance OwlPretty (Name a) where
    owlpretty v = pretty $ show v

instance (OwlPretty a, OwlPretty b) => OwlPretty (a, b) where
    owlpretty (x, y) = parens $ owlpretty x <> pretty "," <+> owlpretty y

instance OwlPretty Idx where
    owlpretty (IVar _ s) = pretty $ show s

owlprettyIdxParams :: ([Idx], [Idx]) -> Doc AnsiStyle
owlprettyIdxParams  ([], []) = mempty
owlprettyIdxParams (vs1, vs2) = pretty "<" <> pretty (intercalate "," (map (show . owlpretty) vs1)) <> pretty "@" <> pretty (intercalate "," (map (show . owlpretty) vs2)) <> pretty ">"

flowColor = Cyan
corrColor = Red

instance  OwlPretty NameExpX where
    owlpretty (PRFName n e) = owlpretty "PRF<" <> owlpretty n <> owlpretty ", " <> owlpretty e <> owlpretty ">"
    owlpretty (NameConst vs n oi) = 
        let pi = case oi of
                   Nothing -> mempty
                   Just (xs, i) -> owlpretty "[" <> hsep (intersperse (pretty ",") (map owlpretty xs)) <> owlpretty ";" <+> owlpretty i <> owlpretty "]"
        in
        owlpretty n <> owlprettyIdxParams vs <> pi

owlprettyBind :: (Alpha a, Alpha b, OwlPretty a, OwlPretty b) => Bind b a -> (OwlDoc, OwlDoc)
owlprettyBind b = 
    let (x, y) = unsafeUnbind b in
    (owlpretty x, owlpretty y)

instance  OwlPretty LblConst where
    owlpretty (TyLabelVar s) = owlpretty s

instance  OwlPretty LabelX where
    owlpretty (LName n) = owlpretty "[" <> owlpretty n <> owlpretty "]"
    owlpretty LZero = owlpretty "static"
    owlpretty (LAdv) = owlpretty "adv"
    owlpretty (LTop) = owlpretty "top"
    owlpretty (LJoin v1 v2) = owlpretty v1 <+> owlpretty "/\\" <+> owlpretty v2
    owlpretty (LConst s) = owlpretty s
    owlpretty (LRangeIdx l) = 
        let (b, l') = owlprettyBind l in
        owlpretty "/\\_" <> b <+> owlpretty "(" <> l' <> owlpretty ")"

instance  OwlPretty (Path) where
    owlpretty (PRes p) = owlpretty p
    owlpretty p = owlpretty $ show p

instance OwlPretty ResolvedPath where
    owlpretty (PDot PTop x) = owlpretty x
    owlpretty (PDot (PPathVar OpenPathVar _) s) = owlpretty s
    owlpretty (PDot (PPathVar (ClosedPathVar s) _) x) = owlpretty (unignore s) <> pretty "." <> owlpretty x
    owlpretty (PDot x y) = owlpretty x <> pretty "." <> owlpretty y

instance  OwlPretty TyX where
    owlpretty TUnit =
        owlpretty "unit"
    owlpretty (TBool l) = 
            owlpretty "Bool<" <> owlpretty l <> owlpretty ">"
    owlpretty (TData l1 l2 _) = 
            if l1 `aeq` l2 then
                owlpretty "Data" <> angles (owlpretty l1)
            else
                owlpretty "Data<" <> owlpretty l1 <> owlpretty ", |" <> owlpretty l2 <> owlpretty "|>"
    owlpretty (TDataWithLength l1 a) = 
            owlpretty "Data <" <> owlpretty l1 <> owlpretty ">" <+> owlpretty "|" <> owlpretty a <> owlpretty "|"
    owlpretty (TRefined t s xp) = 
        let (x, p) = owlprettyBind xp in
        owlpretty s <> owlpretty ":" <> parens (owlpretty t) <> braces (align p)
    owlpretty (TOption t) = 
            owlpretty "Option" <+> owlpretty t
    owlpretty (TCase p t1 t2) = 
            owlpretty "if" <+> owlpretty p <+> owlpretty "then" <+> owlpretty t1 <> owlpretty " else " <> owlpretty t2 
    owlpretty (TConst n ps) =
            owlpretty n <> owlpretty "<" <> hsep (intersperse (pretty ",") (map owlpretty ps))  <> owlpretty ">"
    owlpretty (TName n) =
            owlpretty "Name(" <> owlpretty n <> owlpretty ")"
    owlpretty (TVK n) =
            owlpretty "vk(" <> owlpretty n <> owlpretty ")"
    owlpretty (TDH_PK n) =
            owlpretty "dhpk(" <> owlpretty n <> owlpretty ")"
    owlpretty (TEnc_PK n) =
            owlpretty "encpk(" <> owlpretty n <> owlpretty ")"
    owlpretty (TSS n m) =
            owlpretty "shared_secret(" <> owlpretty n <> owlpretty ", " <> owlpretty m <> owlpretty ")"
    owlpretty TAdmit = owlpretty "admit"
    owlpretty (TExistsIdx it) = 
        let (i, t) = owlprettyBind it in
        owlpretty "exists" <+> i <> owlpretty "." <+> t
    owlpretty (TUnion t1 t2) =
        owlpretty "Union<" <> owlpretty t1 <> owlpretty "," <> owlpretty t2 <> owlpretty ">"

instance  OwlPretty Quant where
    owlpretty Forall = owlpretty "forall"
    owlpretty Exists = owlpretty "exists"

pIsInfix :: Prop -> Bool
pIsInfix (Spanned _ (PAnd _ _)) = True
pIsInfix (Spanned _ (POr _ _)) = True
pIsInfix (Spanned _ (PImpl _ _)) = True
pIsInfix _ = False

pIsAnd :: Prop -> Bool
pIsAnd (Spanned _ (PAnd _ _)) = True
pIsAnd _ = False

pIsOr :: Prop -> Bool
pIsOr (Spanned _ (POr _ _)) = True
pIsOr _ = False

instance  OwlPretty PropX where 
    owlpretty PTrue = owlpretty "true"
    owlpretty PFalse = owlpretty "false"
    owlpretty (PAnd p1 p2) = 
        let pp1 = if (pIsInfix p1 && (not $ pIsAnd p1)) then parens (owlpretty p1) else owlpretty p1 in
        let pp2 = if (pIsInfix p2 && (not $ pIsAnd p2)) then parens (owlpretty p2) else owlpretty p2 in
        pp1 <+> owlpretty "/\\" <+> pp2
    owlpretty (POr p1 p2) = 
        let pp1 = if (pIsInfix p1 && (not $ pIsOr p1)) then parens (owlpretty p1) else owlpretty p1 in
        let pp2 = if (pIsInfix p2 && (not $ pIsOr p2)) then parens (owlpretty p2) else owlpretty p2 in
        pp1 <+> owlpretty "\\/" <+> pp2
    owlpretty (PNot (Spanned _ (PEq a b))) = owlpretty a <+> owlpretty "!=" <+> owlpretty b
    owlpretty (PEq e1 e2) = owlpretty e1 <+> owlpretty "==" <+> owlpretty e2
    owlpretty (PEqIdx e1 e2) = owlpretty e1 <+> owlpretty "=idx" <+> owlpretty e2
    owlpretty (PLetIn a xe2) = 
        let (x, e2) = owlprettyBind xe2 in
        owlpretty "let" <+> x <+> owlpretty "=" <+> owlpretty a <+> owlpretty "in" <+> e2
    owlpretty (PImpl p1 p2) = 
        let pp1 = if (pIsInfix p1) then parens (owlpretty p1) else owlpretty p1 in
        let pp2 = if (pIsInfix p2) then parens (owlpretty p2) else owlpretty p2 in
        pp1 <+> owlpretty "==>" <+> pp2
    owlpretty (PNot (Spanned _ (PFlow l1 l2))) = annotate (color flowColor) $ owlpretty l1 <+> owlpretty "!<=" <+> owlpretty l2
    owlpretty (PFlow l1 l2) = annotate (color flowColor) $ owlpretty l1 <+> owlpretty "<=" <+> owlpretty l2
    owlpretty (PIsConstant a) = owlpretty "is_constant(" <> owlpretty a <> owlpretty ")"
    owlpretty (PQuantIdx q b) = 
        let (x, p) = owlprettyBind b in
        owlpretty q <+> x <+> owlpretty ": idx" <> owlpretty "." <+> p
    owlpretty (PQuantBV q b) = 
        let (x, p) = owlprettyBind b in
        owlpretty q <+> x <+> owlpretty ": bv" <> owlpretty "." <+> p
    owlpretty (PRO a b i) = owlpretty "ro(" <> owlpretty a <> owlpretty "," <+> owlpretty b <> owlpretty "," <+> owlpretty i <> owlpretty ")"
    owlpretty (PApp p is xs) = owlpretty p <> angles (mconcat $ map owlpretty is) <> list (map owlpretty xs)
    owlpretty (PAADOf ne x) = owlpretty "aad" <> tupled [owlpretty ne] <> brackets (owlpretty x)
    owlpretty (PHappened s ixs xs) = 
        let pids = 
                case ixs of
                  ([], []) -> mempty
                  (v1, v2) -> owlpretty "<" <> 
                         owlpretty (intercalate "," (map (show . owlpretty) v1)) <> 
                         owlpretty "@" <>
                         owlpretty (intercalate "," (map (show . owlpretty) v2)) <> 
                         owlpretty ">" in 
        owlpretty "happened(" <> owlpretty s <> pids <> tupled (map owlpretty xs) <> owlpretty ")"
    owlpretty (PNot p) = owlpretty "!" <+> owlpretty p

instance  OwlPretty NameTypeX where
    owlpretty (NT_Sig ty) = owlpretty "sig" <+> owlpretty ty
    owlpretty (NT_StAEAD ty xaad p pat) = 
        let (x, aad) = owlprettyBind xaad in
        owlpretty "StAEAD" <+> owlpretty ty <+> owlpretty "(" <> x <> owlpretty "." <> aad <> owlpretty ")" <+> owlpretty p
    owlpretty (NT_Enc ty) = owlpretty "enc" <+> owlpretty ty
    owlpretty (NT_PKE ty) = owlpretty "pke" <+> owlpretty ty
    owlpretty (NT_MAC ty) = owlpretty "mac" <+> owlpretty ty
    owlpretty (NT_PRF xs) = owlpretty "prf" <+> owlpretty "[" <> hsep (map (\(ae, nt) -> owlpretty ae <+> owlpretty "->" <+> owlpretty nt) xs) <> owlpretty "]"
    owlpretty NT_DH = owlpretty "DH"
    owlpretty NT_Nonce = owlpretty "nonce"


instance  OwlPretty AExprX where
    owlpretty (AEVar s n) = owlpretty (unignore s)
    owlpretty (AEApp f _ as) = 
        case (f, as) of
          (PRes (PDot PTop "plus"), [x, y]) -> owlpretty x <+> owlpretty "+" <+> owlpretty y
          (PRes (PDot PTop "concat"), [x, y]) -> owlpretty x <+> owlpretty "++" <+> owlpretty y
          (PRes (PDot PTop "zero"), []) -> owlpretty "0"
          (PRes (PDot PTop s), xs) -> owlpretty s <> tupled (map owlpretty xs)
          _ -> owlpretty f <> pretty "(" <> mconcat (map owlpretty as) <> pretty ")"
    owlpretty (AEHex s) = owlpretty "0x" <> owlpretty s
    owlpretty (AELenConst s) = owlpretty "|" <> owlpretty s <> owlpretty "|"
    owlpretty (AEInt i) = owlpretty i
    owlpretty (AEPreimage p ps xs) = 
        let pxs = case xs of
                    [] -> mempty
                    _ -> owlpretty xs
        in
        owlpretty "preimage" <> owlprettyIdxParams ps <> owlpretty "(" <> owlpretty p <> owlpretty ")" <> pxs
    owlpretty (AEGet ne) = owlpretty "get" <> owlpretty "(" <> owlpretty ne <> owlpretty ")"
    owlpretty (AEGetEncPK ne) = owlpretty "get_encpk" <> owlpretty "(" <> owlpretty ne <> owlpretty ")"
    owlpretty (AEGetVK ne) = owlpretty "get_vk" <> owlpretty "(" <> owlpretty ne <> owlpretty ")"
    owlpretty (AEPackIdx s a) = owlpretty "pack" <> owlpretty "<" <> owlpretty s <> owlpretty ">(" <> owlpretty a <> owlpretty ")"

instance  OwlPretty BuiltinLemma where
    owlpretty (LemmaConstant) = owlpretty "is_constant_lemma"
    owlpretty (LemmaDisjNotEq) = owlpretty "disjoint_not_eq_lemma" 
    owlpretty (LemmaCrossDH n1 n2 n3) = owlpretty "cross_dh_lemma" <> angles (tupled [owlpretty n1, owlpretty n2, owlpretty n3])
    owlpretty (LemmaCRH) = owlpretty "crh_lemma"

instance  OwlPretty CryptOp where
    owlpretty (CHash _ _) = owlpretty "hash"
    owlpretty (CPRF x) = 
        owlpretty "PRF" <+> owlpretty x 
    owlpretty (CLemma l) = owlpretty l
    owlpretty (CAEnc) = owlpretty "aenc"
    owlpretty (CADec) = owlpretty "adec"
    owlpretty CPKEnc = owlpretty "pkenc"
    owlpretty CPKDec = owlpretty "pkdec"
    owlpretty CMac = owlpretty "mac"
    owlpretty CMacVrfy = owlpretty "mac_vrfy"
    owlpretty CSign = owlpretty "sign"
    owlpretty CSigVrfy = owlpretty "vrfy"
    owlpretty (CEncStAEAD p (idx1, idx2)) = owlpretty "st_aead_enc" <> angles (owlpretty p <> angles (tupled (map owlpretty idx1) <> owlpretty "@" <> tupled (map owlpretty idx2)))
    owlpretty (CDecStAEAD) = owlpretty "st_aead_dec"

instance  OwlPretty ExprX where 
    owlpretty (ECrypt cop as) = 
        owlpretty cop <> (tupled (map owlpretty as))
    owlpretty (EInput _ k) = 
        let ((x, i), e) = unsafeUnbind k in
        owlpretty "input" <+> owlpretty x <> owlpretty ", " <> owlpretty i <> owlpretty " in " <> owlpretty e
    owlpretty (EOutput e l) = owlpretty "output" <+> owlpretty e <+> (case l of
       Nothing -> owlpretty ""
       Just s -> owlpretty "to" <+> owlpretty s)
    owlpretty (EBlock e) = owlpretty "{" <> owlpretty e <> owlpretty "}"
    owlpretty (ELet e1 tyAnn anf sx xk) = 
        let (x, k) = owlprettyBind xk in
        let tann = case tyAnn of
                     Nothing -> mempty
                     Just t -> owlpretty ":" <+> owlpretty t
        in
        let anfLet = case anf of
                        Nothing -> owlpretty "let"
                        Just a -> owlpretty "anf_let[" <> owlpretty a <> owlpretty "]"
        in
        anfLet <+> owlpretty sx <+> tann <+> owlpretty "=" <+> owlpretty "(" <> owlpretty e1 <> owlpretty ")" <+> owlpretty "in" <> line <> k
    owlpretty (EUnionCase a _ xk) = 
        let (x, k) = owlprettyBind xk in
        owlpretty "union_case" <+> x <+> owlpretty "=" <> owlpretty a <+>  owlpretty "in" <+> k
    owlpretty (EUnpack a k) = owlpretty "unpack a .... TODO"
    owlpretty (EIf t e1 e2) = 
        owlpretty "if" <+> owlpretty t <+> owlpretty "then" <+> owlpretty e1 <+> owlpretty "else" <+> owlpretty e2
    owlpretty (EForallBV xpk) = owlpretty "forall_expr.. TODO" 
    owlpretty (EForallIdx xpk) = owlpretty "forall_idx.. TODO"
    owlpretty (EGuard a e) = 
        owlpretty "guard" <+> owlpretty a <+> owlpretty "in" <+> owlpretty e
    owlpretty (ERet ae) = owlpretty ae
    owlpretty (EAdmit) = owlpretty "admit"
    owlpretty (ECall f is as) = 
        let inds = case is of
                     ([], []) -> mempty
                     (v1, v2) -> owlpretty "<" <> mconcat (map owlpretty v1) <> owlpretty "@" <> mconcat (map owlpretty v2) <> owlpretty ">"
        in
        owlpretty "call" <> inds <+> owlpretty f <> tupled (map owlpretty as)
    owlpretty (ECase t xs) = 
        let pcases = 
                map (\(c, o) -> 
                    case o of
                      Left e -> owlpretty "|" <+> owlpretty c <+> owlpretty "=>" <+> owlpretty e
                      Right (_, xe) -> let (x, e) = owlprettyBind xe in owlpretty "|" <+> owlpretty c <+> x <+> owlpretty "=>" <+> e
                    ) xs in
        owlpretty "case" <+> owlpretty t <> line <> vsep pcases
    owlpretty (EPCase p op e) = 
        owlpretty "pcase" <+> parens (owlpretty p) <+> owlpretty "in" <+> owlpretty e
    owlpretty (EDebug dc) = owlpretty "debug" <+> owlpretty dc
    owlpretty (ESetOption s1 s2 e) = owlpretty "set_option" <+> owlpretty (show s1) <+> owlpretty "=" <+> owlpretty (show s2) <+> owlpretty "in" <+> owlpretty e                                         
    owlpretty (EAssert p) = owlpretty "assert" <+> owlpretty p
    owlpretty (EAssume p) = owlpretty "assume" <+> owlpretty p
    owlpretty (EFalseElim k) = owlpretty "false_elim in" <+> owlpretty k
    owlpretty (ETLookup n a) = owlpretty "lookup" <> tupled [owlpretty a]
    owlpretty (ETWrite n a a') = owlpretty "write" <> tupled [owlpretty a, owlpretty a']
    owlpretty _ = owlpretty "unimp"

instance  OwlPretty DebugCommand where
    owlpretty (DebugPrintTyOf ae) = owlpretty "debugPrintTyOf(" <> owlpretty ae <> owlpretty ")"
    owlpretty (DebugPrint s) = owlpretty "debugPrint(" <> owlpretty s <> owlpretty ")"
    owlpretty (DebugPrintTy t) = owlpretty "debugPrintTy(" <> owlpretty t <> owlpretty ")"
    owlpretty (DebugPrintProp t) = owlpretty "debugPrintProp(" <> owlpretty t <> owlpretty ")"
    owlpretty (DebugPrintTyContext anf) = owlpretty "debugPrintTyContext" <+> (if anf then owlpretty "anf" else mempty)
    owlpretty (DebugPrintExpr e) = owlpretty "debugPrintExpr(" <> owlpretty e <> owlpretty ")"
    owlpretty (DebugPrintLabel l) = owlpretty "debugPrintLabel(" <> owlpretty l <> owlpretty ")"
    owlpretty (DebugResolveANF a) = owlpretty "resolveANF" <> parens (owlpretty a)

instance  OwlPretty FuncParam where
    owlpretty (ParamStr s) = owlpretty s
    owlpretty (ParamAExpr a) = owlpretty a
    owlpretty (ParamLbl l) = owlpretty l
    owlpretty (ParamTy t) = owlpretty t
    owlpretty (ParamIdx i) = owlpretty i
    owlpretty (ParamName ne) = owlpretty ne

instance  OwlPretty Endpoint where
    owlpretty (Endpoint  x) = owlpretty x
    owlpretty (EndpointLocality l) = owlpretty "endpoint(" <> owlpretty l <> owlpretty ")"

instance  OwlPretty Locality where
    owlpretty (Locality s xs) = owlpretty s <> angles (mconcat $ map owlpretty xs)

instance  OwlPretty DeclX where
    owlpretty d = owlpretty (show d)

instance  OwlPretty ModuleExpX where
    owlpretty (ModuleBody _ nk) = 
        let (n, k) = owlprettyBind nk in
        angles (n <> owlpretty "." <> k)
    owlpretty (ModuleVar p) = owlpretty p
    owlpretty x = owlpretty $ show x

