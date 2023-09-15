module Pretty where
import AST
import Prettyprinter
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Unsafe
import Data.List

instance Pretty a => Pretty (Spanned a) where
    pretty (Spanned _ v) = pretty v

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
                   Just (xs, i) -> pretty "[" <> hsep (intersperse (pretty ",") (map pretty xs)) <> pretty ";" <+> pretty i <> pretty "]"
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
    pretty (LTop) = pretty "top"
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
    pretty (TRefined t s xp) = 
        let (x, p) = prettyBind xp in
        pretty s <> pretty ":" <> parens (pretty t) <> braces (align p)
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

instance Pretty PropX where 
    pretty PTrue = pretty "true"
    pretty PFalse = pretty "false"
    pretty (PAnd p1 p2) = 
        let pp1 = if (pIsInfix p1 && (not $ pIsAnd p1)) then parens (pretty p1) else pretty p1 in
        let pp2 = if (pIsInfix p2 && (not $ pIsAnd p2)) then parens (pretty p2) else pretty p2 in
        pp1 <+> pretty "/\\" <+> pp2
    pretty (POr p1 p2) = 
        let pp1 = if (pIsInfix p1 && (not $ pIsOr p1)) then parens (pretty p1) else pretty p1 in
        let pp2 = if (pIsInfix p2 && (not $ pIsOr p2)) then parens (pretty p2) else pretty p2 in
        pp1 <+> pretty "\\/" <+> pp2
    pretty (PNot (Spanned _ (PEq a b))) = pretty a <+> pretty "!=" <+> pretty b
    pretty (PEq e1 e2) = pretty e1 <+> pretty "==" <+> pretty e2
    pretty (PEqIdx e1 e2) = pretty e1 <+> pretty "=idx" <+> pretty e2
    pretty (PLetIn a xe2) = 
        let (x, e2) = prettyBind xe2 in
        pretty "let" <+> x <+> pretty "=" <+> pretty a <+> pretty "in" <+> e2
    pretty (PImpl p1 p2) = 
        let pp1 = if (pIsInfix p1) then parens (pretty p1) else pretty p1 in
        let pp2 = if (pIsInfix p2) then parens (pretty p2) else pretty p2 in
        pp1 <+> pretty "==>" <+> pp2
    pretty (PNot (Spanned _ (PFlow l1 l2))) = pretty l1 <+> pretty "!<=" <+> pretty l2
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
    pretty (PAADOf ne x) = pretty "aad" <> tupled [pretty ne] <> brackets (pretty x)
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
    pretty (PNot p) = pretty "!" <+> pretty p

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
    pretty (AEApp f _ as) = 
        case (f, as) of
          (PRes (PDot PTop "plus"), [x, y]) -> pretty x <+> pretty "+" <+> pretty y
          (PRes (PDot PTop "concat"), [x, y]) -> pretty x <+> pretty "++" <+> pretty y
          (PRes (PDot PTop "zero"), []) -> pretty "0"
          (PRes (PDot PTop s), xs) -> pretty s <> tupled (map pretty xs)
          _ -> pretty f <> tupled (map pretty as)
    pretty (AEHex s) = pretty "0x" <> pretty s
    pretty (AELenConst s) = pretty "|" <> pretty s <> pretty "|"
    pretty (AEInt i) = pretty i
    pretty (AEPreimage p ps xs) = 
        let pxs = case xs of
                    [] -> mempty
                    _ -> pretty xs
        in
        pretty "preimage" <> prettyIdxParams ps <> pretty "(" <> pretty p <> pretty ")" <> pxs
    pretty (AEGet ne) = pretty "get" <> pretty "(" <> pretty ne <> pretty ")"
    pretty (AEGetEncPK ne) = pretty "get_encpk" <> pretty "(" <> pretty ne <> pretty ")"
    pretty (AEGetVK ne) = pretty "get_vk" <> pretty "(" <> pretty ne <> pretty ")"
    pretty (AEPackIdx s a) = pretty "pack" <> pretty "<" <> pretty s <> pretty ">(" <> pretty a <> pretty ")"

instance Pretty BuiltinLemma where
    pretty (LemmaConstant) = pretty "is_constant_lemma"
    pretty (LemmaDisjNotEq) = pretty "disjoint_not_eq_lemma" 
    pretty (LemmaCrossDH n1 n2 n3) = pretty "cross_dh_lemma" <> angles (tupled [pretty n1, pretty n2, pretty n3])
    pretty (LemmaCRH) = pretty "crh_lemma"

instance Pretty CryptOp where
    pretty (CHash _ _) = pretty "hash"
    pretty (CPRF x) = 
        pretty "PRF" <+> pretty x 
    pretty (CLemma l) = pretty l
    pretty (CAEnc) = pretty "aenc"
    pretty (CADec) = pretty "adec"
    pretty CPKEnc = pretty "pkenc"
    pretty CPKDec = pretty "pkdec"
    pretty CMac = pretty "mac"
    pretty CMacVrfy = pretty "mac_vrfy"
    pretty CSign = pretty "sign"
    pretty CSigVrfy = pretty "vrfy"
    pretty (CEncStAEAD p (idx1, idx2)) = pretty "st_aead_enc" <> angles (pretty p <> angles (tupled (map pretty idx1) <> pretty "@" <> tupled (map pretty idx2)))
    pretty (CDecStAEAD) = pretty "st_aead_dec"

instance Pretty ExprX where 
    pretty (ECrypt cop as) = 
        pretty cop <> (tupled (map pretty as))
    pretty (EInput _ k) = 
        let ((x, i), e) = unsafeUnbind k in
        pretty "input" <+> pretty x <> pretty ", " <> pretty i <> pretty " in " <> pretty e
    pretty (EOutput e l) = pretty "output" <+> pretty e <+> (case l of
       Nothing -> pretty ""
       Just s -> pretty "to" <+> pretty s)
    pretty (EBlock e) = pretty "{" <> pretty e <> pretty "}"
    pretty (ELet e1 tyAnn anf sx xk) = 
        let (x, k) = prettyBind xk in
        let tann = case tyAnn of
                     Nothing -> mempty
                     Just t -> pretty ":" <+> pretty t
        in
        let anfLet = case anf of
                        Nothing -> pretty "let"
                        Just a -> pretty "anf_let[" <> pretty a <> pretty "]"
        in
        anfLet <+> pretty sx <+> tann <+> pretty "=" <+> pretty "(" <> pretty e1 <> pretty ")" <+> pretty "in" <> line <> k
    pretty (EUnionCase a xk) = 
        let (x, k) = prettyBind xk in
        pretty "union_case" <+> x <+> pretty "=" <> pretty a <+>  pretty "in" <+> k
    pretty (EUnpack a k) = pretty "unpack a .... TODO"
    pretty (EIf t e1 e2) = 
        pretty "if" <+> pretty t <+> pretty "then" <+> pretty e1 <+> pretty "else" <+> pretty e2
    pretty (EForallBV xpk) = pretty "forall_expr.. TODO" 
    pretty (EForallIdx xpk) = pretty "forall_idx.. TODO"
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
        pretty "pcase" <+> parens (pretty p) <+> pretty "in" <+> pretty e
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
    pretty (DebugPrintTyContext anf) = pretty "debugPrintTyContext" <+> (if anf then pretty "anf" else mempty)
    pretty (DebugPrintExpr e) = pretty "debugPrintExpr(" <> pretty e <> pretty ")"
    pretty (DebugPrintLabel l) = pretty "debugPrintLabel(" <> pretty l <> pretty ")"
    pretty (DebugResolveANF a) = pretty "resolveANF" <> parens (pretty a)

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

