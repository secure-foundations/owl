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
import qualified Data.Text as T
import qualified Prettyprinter.Render.Text as T

type OwlDoc = Doc AnsiStyle

class OwlPretty a where
    owlpretty' :: Bool -> a -> Doc AnsiStyle
    owlpretty :: a -> Doc AnsiStyle
    owlpretty = owlpretty' False
    owlprettyTimestamp :: a -> Doc AnsiStyle
    owlprettyTimestamp = owlpretty' True

instance OwlPretty Char where
    owlpretty' _ = pretty

instance OwlPretty a => OwlPretty (Ignore a) where
    owlpretty' b x = owlpretty' b (unignore x)

instance OwlPretty Bool where
    owlpretty' _ = pretty

instance OwlPretty Int where
    owlpretty' _ = pretty

instance OwlPretty a => OwlPretty [a] where
    owlpretty' b = mconcat . map (owlpretty' b)

instance OwlPretty a => OwlPretty (Maybe a) where
    owlpretty' _ Nothing = mempty
    owlpretty' b (Just x) = owlpretty' b x

instance OwlPretty a => OwlPretty (Spanned a) where
    owlpretty' b (Spanned _ v) = owlpretty' b v

instance OwlPretty a => OwlPretty (Timestamped a) where
    owlpretty' False (Timestamped _ v) = owlpretty' False v
    owlpretty' True (Timestamped t v) = owlpretty t <> owlpretty ":" <+> owlpretty' True v

instance OwlPretty Position where
    owlpretty' _ = pretty

instance OwlPretty (Name a) where
    owlpretty' _ v = pretty $ show v

instance (OwlPretty a, OwlPretty b) => OwlPretty (a, b) where
    owlpretty' b (x, y) = parens $ owlpretty' b x <> pretty "," <+> owlpretty' b y

instance OwlPretty Idx where
    owlpretty' _ (IVar _ s _) = pretty $ unignore s

owlprettyIdxParams :: ([Idx], [Idx]) -> Doc AnsiStyle
owlprettyIdxParams  ([], []) = mempty
owlprettyIdxParams (vs1, vs2) = pretty "<" <> pretty (intercalate "," (map (show . owlpretty) vs1)) <> pretty "@" <> pretty (intercalate "," (map (show . owlpretty) vs2)) <> pretty ">"

flowColor = Cyan
corrColor = Red
tyColor = Magenta

owlprettyKDFSelector :: KDFSelector -> OwlDoc
owlprettyKDFSelector (i, []) = owlpretty i
owlprettyKDFSelector (i, xs) = owlpretty i <> angles (mconcat $ intersperse (owlpretty ",") (map owlpretty xs))

instance  OwlPretty NameExpX where
    owlpretty' _ (KDFName a b c nks j nt _) = 
        Prettyprinter.group $ 
        owlpretty "KDF<" <> (mconcat $ intersperse (owlpretty "||") (map owlpretty nks))
                            <>
                            owlpretty ";"
                            <>
                            owlpretty j
                            <>
                            owlpretty ";"
                            <>
                            -- (flatAlt (owlpretty "<nametype>") (owlpretty nt))
                            owlpretty nt
                            <> owlpretty ">"
                            <> tupled (map owlpretty [a, b, c])
    owlpretty' _ (NameConst vs n xs) = 
        let pxs = case xs of
                    [] -> mempty
                    _ -> list (map owlpretty xs)
        in
        owlpretty n <> owlprettyIdxParams vs <> pxs
                                                     
owlprettyBind' :: (Alpha a, Alpha b, OwlPretty a, OwlPretty b) => Bool -> Bind b a -> (OwlDoc, OwlDoc)
owlprettyBind' showTs b = 
    let (x, y) = unsafeUnbind b in
    (owlpretty' showTs x, owlpretty' showTs y)

owlprettyBind :: (Alpha a, Alpha b, OwlPretty a, OwlPretty b) => Bind b a -> (OwlDoc, OwlDoc)
owlprettyBind = owlprettyBind' False

owlprettyTimestampBind :: (Alpha a, Alpha b, OwlPretty a, OwlPretty b) => Bind b a -> (OwlDoc, OwlDoc)
owlprettyTimestampBind = owlprettyBind' True

instance  OwlPretty LblConst where
    owlpretty' _ (TyLabelVar s) = owlpretty s

instance  OwlPretty LabelX where
    owlpretty' _ (LName n) = owlpretty "[" <> owlpretty n <> owlpretty "]"
    owlpretty' _ LZero = owlpretty "static"
    owlpretty' _ (LAdv) = owlpretty "adv"
    owlpretty' _ (LGhost) = owlpretty "ghost"
    owlpretty' _ (LTop) = owlpretty "top"
    owlpretty' _ (LJoin v1 v2) = owlpretty v1 <+> owlpretty "/\\" <+> owlpretty v2
    owlpretty' _ (LConst s) = owlpretty s
    owlpretty' b (LRangeIdx l) = 
        let (b', l') = owlprettyBind' b l in
        owlpretty "/\\_" <> b' <+> owlpretty "(" <> l' <> owlpretty ")"
    owlpretty' b (LRangeVar l) = 
        let (b', l') = owlprettyBind' b l in
        owlpretty "/\\_" <> b' <+> owlpretty "(" <> l' <> owlpretty ")"

instance  OwlPretty (Path) where
    owlpretty' b (PRes p) = owlpretty' b p
    owlpretty' _ p = owlpretty $ show p

instance OwlPretty ResolvedPath where
    owlpretty' _ (PDot PTop x) = owlpretty x
    owlpretty' _ (PDot (PPathVar OpenPathVar _) s) = owlpretty s
    owlpretty' _ (PDot (PPathVar (ClosedPathVar s) _) x) = owlpretty (unignore s) <> pretty "." <> owlpretty x
    owlpretty' _ (PDot x y) = owlpretty x <> pretty "." <> owlpretty y

instance OwlPretty Timestamp where
    owlpretty' _ (Timestamp ts) = owlpretty "@[" <> owlpretty ts <> owlpretty "]"

instance OwlPretty TimestampConstraint where
    owlpretty' _ (TimestampLeq t1 t2) = owlpretty t1 <+> owlpretty "<=" <+> owlpretty t2

instance  OwlPretty TyX where
    owlpretty' b t = annotate (color tyColor) $ 
        case t of
            TUnit ->
                owlpretty "unit"
            (TBool l) -> 
                owlpretty "Bool<" <> owlpretty l <> owlpretty ">"
            (TGhost) -> owlpretty "Ghost"
            (TData l1 l2 _) -> 
                if l1 `aeq` l2 then
                    owlpretty "Data" <> angles (owlpretty l1)
                else
                    owlpretty "Data<" <> owlpretty l1 <> owlpretty ", |" <> owlpretty l2 <> owlpretty "|>"
            (TDataWithLength l1 a) -> 
                owlpretty "Data <" <> owlpretty l1 <> owlpretty ">" <+> owlpretty "|" <> owlpretty a <> owlpretty "|"
            (TRefined t s xp) -> 
                let (x, p) = owlprettyBind' b xp in
                owlpretty s <> owlpretty ":" <> parens (owlpretty' b t) <> braces (nest 6 p)
            (TOption t) -> 
                    owlpretty "Option" <+> owlpretty' b t
            (TCase p t1 t2) -> 
                    owlpretty "if" <+> owlpretty' b p <+> owlpretty "then" <+> owlpretty' b t1 <> owlpretty " else " <> owlpretty' b t2 
            (TConst n ps) ->
                    let args = 
                            case ps of 
                              [] -> mempty
                              _ -> owlpretty "<" <> hsep (intersperse (pretty ",") (map (owlpretty' b) ps))  <> owlpretty ">"
                    in
                    owlpretty n <> args
            (TName n) ->
                    owlpretty "Name(" <> owlpretty n <> owlpretty ")"
            (TVK n) ->
                    owlpretty "vk(" <> owlpretty n <> owlpretty ")"
            (TDH_PK n) ->
                    owlpretty "dhpk(" <> owlpretty n <> owlpretty ")"
            (TEnc_PK n) ->
                    owlpretty "encpk(" <> owlpretty n <> owlpretty ")"
            (TSS n m) ->
                    owlpretty "shared_secret(" <> owlpretty n <> owlpretty ", " <> owlpretty m <> owlpretty ")"
            TAdmit -> owlpretty "admit"
            (TExistsIdx _ it) -> 
                let (i, t) = owlprettyBind' b it in
                owlpretty "exists" <+> i <> owlpretty "." <+> t
            (THexConst a) ->
                owlpretty "Const(" <> owlpretty "0x" <> owlpretty a <> owlpretty ")"

instance  OwlPretty Quant where
    owlpretty' _ Forall = owlpretty "forall"
    owlpretty' _ Exists = owlpretty "exists"

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

instance OwlPretty NameKind where
    owlpretty' _ n = 
        owlpretty $ case n of
                      NK_KDF -> "kdfkey"
                      NK_DH -> "dhkey"
                      NK_Enc -> "enckey"
                      NK_PKE -> "pkekey"
                      NK_Sig -> "sigkey"
                      NK_MAC -> "mackey"
                      NK_Nonce len -> 
                          case len of
                            "nonce" -> "nonce"
                            _ -> "nonce |" ++ len ++ "|"

newtype NameKindRow = NameKindRow [NameKind]
instance OwlPretty NameKindRow where
    owlpretty' b (NameKindRow n) = mconcat $ intersperse (owlpretty "||") (map (owlpretty' b) n)


instance  OwlPretty PropX where 
    owlpretty' b PTrue = owlpretty "true"
    owlpretty' b PFalse = owlpretty "false"
    owlpretty' b (PAnd p1 p2) = 
        let pp1 = if (pIsInfix p1 && (not $ pIsAnd p1)) then parens (owlpretty' b p1) else owlpretty' b p1 in
        let pp2 = if (pIsInfix p2 && (not $ pIsAnd p2)) then parens (owlpretty' b p2) else owlpretty' b p2 in
        pp1 <+> owlpretty "/\\" <+> pp2
    owlpretty' b (POr p1 p2) = 
        let pp1 = if (pIsInfix p1 && (not $ pIsOr p1)) then parens (owlpretty' b p1) else owlpretty' b p1 in
        let pp2 = if (pIsInfix p2 && (not $ pIsOr p2)) then parens (owlpretty' b p2) else owlpretty' b p2 in
        pp1 <+> owlpretty "\\/" <+> pp2
    owlpretty' _ (PNot (Spanned _ (PEq a b))) = owlpretty a <+> owlpretty "!=" <+> owlpretty b
    owlpretty' _ (PEq e1 e2) = owlpretty e1 <+> owlpretty "==" <+> owlpretty e2
    owlpretty' _ (PNot (Spanned _ (PEqIdx e1 e2))) = annotate (color flowColor) $ owlpretty e1 <+> owlpretty "!=idx" <+> owlpretty e2
    owlpretty' _ (PEqIdx e1 e2) = annotate (color flowColor) $ owlpretty e1 <+> owlpretty "=idx" <+> owlpretty e2
    owlpretty' b (PLetIn a xe2) = 
        let (x, e2) = owlprettyBind' b xe2 in
        owlpretty "let" <+> x <+> owlpretty "=" <+> owlpretty a <+> owlpretty "in" <+> e2
    owlpretty' b (PImpl p1 p2) = 
        let pp1 = if (pIsInfix p1) then parens (owlpretty' b p1) else owlpretty' b p1 in
        let pp2 = if (pIsInfix p2) then parens (owlpretty' b p2) else owlpretty' b p2 in
        pp1 <+> owlpretty "==>" <+> pp2
    owlpretty' _ (PNot (Spanned _ (PFlow l1 l2))) = annotate (color flowColor) $ owlpretty l1 <+> owlpretty "!<=" <+> owlpretty l2
    owlpretty' _ (PFlow l1 l2) = annotate (color flowColor) $ owlpretty l1 <+> owlpretty "<=" <+> owlpretty l2
    owlpretty' _ (PIsConstant a) = owlpretty "is_constant(" <> owlpretty a <> owlpretty ")"
    owlpretty' b (PQuantIdx q sx bnd) = 
        let (x, p) = owlprettyBind' b bnd in
        owlpretty q <+> owlpretty sx <+> owlpretty ": idx" <> owlpretty "." <+> p
    owlpretty' b (PQuantBV q sx bnd) = 
        let (x, p) = owlprettyBind' b bnd in
        owlpretty q <+> owlpretty sx <+> owlpretty ": bv" <> owlpretty "." <+> p
    owlpretty' _ (PApp p is xs) = owlpretty p <> angles (mconcat $ intersperse (owlpretty ", ") $ map owlpretty is) <> list (map owlpretty xs)
    owlpretty' _ (PAADOf ne x) = owlpretty "aad" <> tupled [owlpretty ne] <> brackets (owlpretty x)
    owlpretty' _ (PInODH s ikm info) = owlpretty "in_odh" <> tupled [owlpretty s, owlpretty ikm, owlpretty info]
    owlpretty' _ (PHonestPKEnc ne a) = owlpretty "honest_pk_enc" <> angles (owlpretty ne) <> tupled [owlpretty a]
    owlpretty' _ (PHappened s ixs xs) = 
        let pids = 
                case ixs of
                  ([], []) -> mempty
                  (v1, v2) -> owlpretty "<" <> 
                         owlpretty (intercalate "," (map (show . owlpretty) v1)) <> 
                         owlpretty "@" <>
                         owlpretty (intercalate "," (map (show . owlpretty) v2)) <> 
                         owlpretty ">" in 
        owlpretty "happened(" <> owlpretty s <> pids <> tupled (map owlpretty xs) <> owlpretty ")"
    owlpretty' b (PNot p) = owlpretty "!" <+> owlpretty' b p

instance OwlPretty KDFStrictness where                                      
    owlpretty' _ (KDFStrict) = owlpretty "strict"
    owlpretty' _ (KDFPub) = owlpretty "public"
    owlpretty' _ KDFUnstrict = mempty

owlprettyIdxBinds1 :: [IdxVar] -> OwlDoc
owlprettyIdxBinds1 [] = mempty
owlprettyIdxBinds1 xs = owlpretty "<" <> hsep (intersperse (owlpretty ",") $ map owlpretty xs) <> owlpretty ">"


instance  OwlPretty NameTypeX where
    owlpretty' _ (NT_KDF kpos cases) = 
        let (((sx, _), (sy, _), (sself, _)), c) = unsafeUnbind cases in 
        let pcases = map (\b ->
                            let (is, (p, nts)) = unsafeUnbind b in 
                            owlprettyIdxBinds1 is <> owlpretty p <+> owlpretty "->" <+> (hsep $ intersperse (owlpretty "||") $
                                                                    map (\(str, nt) -> owlpretty str <+> owlpretty nt) nts)) c
        in
        let hd = case kpos of
                   KDF_SaltPos -> owlpretty "KDF"
                   KDF_IKMPos -> owlpretty "DualKDF"
        in
        hd <> owlpretty "{" <> owlpretty sx <> owlpretty sy <> owlpretty sself <> owlpretty "." <> nest 4 (vsep pcases) <> owlpretty "}"
    owlpretty' _ (NT_Sig ty) = owlpretty "sig" <+> owlpretty ty
    owlpretty' b (NT_StAEAD ty xaad p pat) = 
        let (x, aad) = owlprettyBind' b xaad in
        let (y, ppat) = owlprettyBind' b pat in 
        owlpretty "st_aead" <+> owlpretty ty <+> 
            nest 4 (owlpretty "aad" <> x <> owlpretty "." <> aad <> line 
                    <> owlpretty "nonce" <+> owlpretty p <> line <>
                    owlpretty "pat" <> y <> ppat
                        )
    owlpretty' _ (NT_Enc ty) = owlpretty "enc" <+> owlpretty ty
    owlpretty' _ (NT_App p is as) = 
        owlpretty p <> owlprettyIdxParams is  <> tupled (map owlpretty as)
    owlpretty' _ (NT_PKE ty) = owlpretty "pke" <+> owlpretty ty
    owlpretty' _ (NT_MAC ty) = owlpretty "mac" <+> owlpretty ty
    -- owlpretty' _ (NT_PRF xs) = owlpretty "prf" <+> owlpretty "[" <> hsep (map (\(ae, nt) -> owlpretty ae <+> owlpretty "->" <+> owlpretty nt) xs) <> owlpretty "]"
    owlpretty' _ NT_DH = owlpretty "DH"
    owlpretty' _ (NT_Nonce l) = 
        case l of
          "nonce" -> owlpretty "nonce"
          _ -> owlpretty $ "nonce |" ++ l ++ "|"


instance  OwlPretty AExprX where
    owlpretty' _ (AEVar s n) = owlpretty (unignore s)
    owlpretty' _ (AEApp f _ as) = 
        Prettyprinter.group $ case (f, as) of
          (PRes (PDot PTop "plus"), [x, y]) -> owlpretty x <+> owlpretty "+" <+> owlpretty y
          (PRes (PDot PTop "concat"), [x, y]) -> owlpretty x <+> owlpretty "++" <+> owlpretty y
          (PRes (PDot PTop "zero"), []) -> owlpretty "0"
          (PRes (PDot PTop s), xs) -> owlpretty s <> tupled (map owlpretty xs)
          _ -> owlpretty f <> tupled (map owlpretty as)
    owlpretty' _ (AEHex s) = 
        let ps = if length s > 6 then owlpretty (take 6 s) <> owlpretty "..."
                                 else owlpretty s
        in 
        owlpretty "0x" <> ps
    owlpretty' _ (AELenConst s) = owlpretty "|" <> owlpretty s <> owlpretty "|"
    owlpretty' _ (AEInt i) = owlpretty i
    owlpretty' _ (AEKDF a b c nks j) = owlpretty "gkdf" <>
        angles ((hsep $ intersperse (owlpretty "||") $ map owlpretty nks) <> owlpretty ";" <> owlpretty j)
        <>
        (Prettyprinter.group $ tupled (map owlpretty [a, b, c]))
    --owlpretty' _ (AEPreimage p ps xs) = 
    --    let pxs = case xs of
    --                [] -> mempty
    --                _ -> owlpretty xs
    --    in
    --    owlpretty "preimage" <> owlprettyIdxParams ps <> owlpretty "(" <> owlpretty p <> owlpretty ")" <> pxs
    owlpretty' _ (AEGet ne) = owlpretty "get" <> owlpretty "(" <> owlpretty ne <> owlpretty ")"
    owlpretty' _ (AEGetEncPK ne) = owlpretty "get_encpk" <> owlpretty "(" <> owlpretty ne <> owlpretty ")"
    owlpretty' _ (AEGetVK ne) = owlpretty "get_vk" <> owlpretty "(" <> owlpretty ne <> owlpretty ")"

instance  OwlPretty BuiltinLemma where
    owlpretty' _ (LemmaConstant) = owlpretty "is_constant_lemma"
    owlpretty' _ (LemmaDisjNotEq) = owlpretty "disjoint_not_eq_lemma" 
    owlpretty' _ (LemmaCrossDH n1) = owlpretty "cross_dh_lemma" <> angles (owlpretty n1) 
    owlpretty' _ (LemmaCRH) = owlpretty "crh_lemma"
    owlpretty' _ (LemmaKDFInj ) = owlpretty "kdf_inj_lemma" 

instance  OwlPretty CryptOp where
    -- owlpretty' _ (CHash _ _) = owlpretty "hash"
    --owlpretty' _ (CPRF x) = 
    --    owlpretty "PRF" <+> owlpretty x 
    owlpretty' _ (CLemma l) = owlpretty l
    owlpretty' _ (CAEnc) = owlpretty "aenc"
    owlpretty' _ (CADec) = owlpretty "adec"
    owlpretty' _ CPKEnc = owlpretty "pkenc"
    owlpretty' _ CPKDec = owlpretty "pkdec"
    owlpretty' _ CMac = owlpretty "mac"
    owlpretty' _ CMacVrfy = owlpretty "mac_vrfy"
    owlpretty' _ CSign = owlpretty "sign"
    owlpretty' _ CSigVrfy = owlpretty "vrfy"
    owlpretty' _ (CKDF _ _ _ _) = owlpretty "kdf"
    owlpretty' _ (CEncStAEAD p (idx1, idx2) _) = owlpretty "st_aead_enc" <> angles (owlpretty p <> angles (tupled (map owlpretty idx1) <> owlpretty "@" <> tupled (map owlpretty idx2)))
    owlpretty' _ (CDecStAEAD) = owlpretty "st_aead_dec"

instance (OwlPretty a, OwlPretty b) => OwlPretty (Either a b) where
    owlpretty' b (Left a) = owlpretty "Left" <+> owlpretty' b a
    owlpretty' b (Right a) = owlpretty "Right" <+> owlpretty' b a

instance  OwlPretty ExprX where 
    owlpretty' b (ECrypt cop as) = 
        owlpretty cop <> (tupled (map owlpretty as))
    owlpretty' b (EInput _ k) = 
        let ((x, i), e) = unsafeUnbind k in
        owlpretty "input" <+> owlpretty x <> owlpretty ", " <> owlpretty i <> owlpretty " in " <> owlpretty' b e
    owlpretty' _ (EOutput e l) = owlpretty "output" <+> owlpretty e <+> (case l of
       Nothing -> owlpretty ""
       Just s -> owlpretty "to" <+> owlpretty s)
    owlpretty' b (EBlock e p) = 
        let pp = if p then owlpretty "proof " else mempty
        in
        pp <> owlpretty "{" <> owlpretty' b e <> owlpretty "}"
    owlpretty' b (ELet e1 tyAnn anf sx xk) = 
        let (x, k) = owlprettyBind' b xk in
        let tann = case tyAnn of
                     Nothing -> mempty
                     Just t -> owlpretty ":" <+> owlpretty t
        in
        let anfLet = case anf of
                        Nothing -> owlpretty "let"
                        Just a -> owlpretty "anf_let[" <> owlpretty a <> owlpretty "]"
        in
        owlpretty "let" <+> owlpretty sx <+> tann <+> owlpretty "=" <+> owlpretty "(" <> owlpretty' b e1 <> owlpretty ")" <+> owlpretty "in" <> line <> k
    owlpretty' _ (EUnpack a s k) = owlpretty "unpack a .... TODO"
    owlpretty' b (EIf t e1 e2) = 
        owlpretty "if" <+> owlpretty t <+> owlpretty "then" <+> owlpretty' b e1 <+> owlpretty "else" <+> owlpretty' b e2
    owlpretty' _ (EForallBV _ xpk) = owlpretty "forall_expr.. TODO" 
    owlpretty' _ (EForallIdx _ xpk) = owlpretty "forall_idx.. TODO"
    owlpretty' b (EGuard a e) = 
        owlpretty "guard" <+> owlpretty a <+> owlpretty "in" <+> owlpretty' b e
    owlpretty' _ (ERet ae) = owlpretty ae
    owlpretty' _ EAdmit = owlpretty "admit"
    owlpretty' _ (ECall f is as) = 
        let inds = case is of
                     ([], []) -> mempty
                     (v1, v2) -> owlpretty "<" <> mconcat (map owlpretty v1) <> owlpretty "@" <> mconcat (map owlpretty v2) <> owlpretty ">"
        in
        owlpretty "call" <> inds <+> owlpretty f <> tupled (map owlpretty as)
    owlpretty' b (ECase t otk xs) = 
        let tyann = case otk of
                      Nothing -> mempty
                      Just (t, _) -> owlpretty "as" <+> owlpretty t
            otherwise = case otk of
                      Nothing -> mempty
                      Just (_, k) -> owlpretty "otherwise =>" <+> owlpretty' b k
            pcases = 
                map (\(c, o) -> 
                    case o of
                      Left e -> owlpretty "|" <+> owlpretty c <+> owlpretty "=>" <+> owlpretty' b e
                      Right (_, xe) -> let (x, e) = owlprettyBind' b xe in owlpretty "|" <+> owlpretty c <+> x <+> owlpretty "=>" <+> e
                    ) xs in
        owlpretty "case" <+> tyann <+> owlpretty' b t <> line <> vsep pcases <+> otherwise
    owlpretty' b (EPCase p op attr e) = 
        owlpretty "pcase" <+> parens (owlpretty' b p) <+> owlpretty "in" <+> owlpretty' b e
    owlpretty' b (EDebug dc) = owlpretty "debug" <+> owlpretty' b dc
    owlpretty' b (ESetOption s1 s2 e) = owlpretty "set_option" <+> owlpretty (show s1) <+> owlpretty "=" <+> owlpretty (show s2) <+> owlpretty "in" <+> owlpretty' b e                                         
    owlpretty' b (EAssert p) = owlpretty "assert" <+> owlpretty' b p
    owlpretty' b (EAssume p) = owlpretty "assume" <+> owlpretty' b p
    owlpretty' b (EFalseElim k p) = owlpretty "false_elim in" <+> owlpretty' b k <+> owlpretty "when" <+> owlpretty' b p
    owlpretty' _ (ETLookup n a) = owlpretty "lookup" <> tupled [owlpretty a]
    owlpretty' _ (ETWrite n a a') = owlpretty "write" <> tupled [owlpretty a, owlpretty a']
    owlpretty' b (EParse a t oth bnd) = 
        let (xs, k) = unsafeUnbind bnd in 
        let o = case oth of
                  Just e1 -> owlpretty "otherwise" <+> owlpretty' b e1
                  Nothing -> mempty
        in
        owlpretty "parse" <+> owlpretty a <+> owlpretty (map fst xs) <+> owlpretty "as" <+> owlpretty t <+> owlpretty "in"
        <+> owlpretty' b k <+> o
    owlpretty' b (EPackIdx i e) = owlpretty "pack" <> angles (owlpretty i) <> tupled [owlpretty' b e]
    owlpretty' _ (ELetGhost a sx xk) = owlpretty "let ghost" <+> owlpretty sx <+> owlpretty "=" <+> owlpretty a
    owlpretty' _ (EChooseBV s ip ik) = owlpretty "choose_bv" <+> owlpretty s
    owlpretty' _ (EChooseIdx s ip ik) = owlpretty "choose_idx" <+> owlpretty s
    owlpretty' _ (EGetCtr p iargs) = owlpretty "get_counter" <+> owlpretty p
    owlpretty' _ (EIncCtr p iargs) = owlpretty "inc_counter" <+> owlpretty p
    owlpretty' _ (ECorrCaseNameOf a op e) = owlpretty "corr_case nameOf" <+> owlpretty a
    owlpretty' _ (EOpenTyOf a e) = owlpretty "openTyOf" <+> owlpretty a

instance  OwlPretty DebugCommand where
    owlpretty' _ (DebugPrintTyOf ae _) = owlpretty "debugPrintTyOf(" <> owlpretty ae <> owlpretty ")"
    owlpretty' _ (DebugPrint s) = owlpretty "debugPrint(" <> owlpretty s <> owlpretty ")"
    owlpretty' _ (DebugPrintTy t) = owlpretty "debugPrintTy(" <> owlpretty t <> owlpretty ")"
    owlpretty' b (DebugDecideProp t) = owlpretty "debugDecideProp(" <> owlpretty' b t <> owlpretty ")"
    owlpretty' _ (DebugPrintTyContext anf) = owlpretty "debugPrintTyContext" <+> (if anf then owlpretty "anf" else mempty)
    owlpretty' b (DebugPrintExpr e) = owlpretty "debugPrintExpr(" <> owlpretty' b e <> owlpretty ")"
    owlpretty' _ (DebugPrintLabel l) = owlpretty "debugPrintLabel(" <> owlpretty l <> owlpretty ")"
    owlpretty' _ (DebugResolveANF a) = owlpretty "resolveANF" <> parens (owlpretty a)
    owlpretty' _ _ = owlpretty "unimp"

instance  OwlPretty FuncParam where
    owlpretty' _ (ParamStr s) = owlpretty s
    owlpretty' _ (ParamAExpr a) = owlpretty a
    owlpretty' _ (ParamLbl l) = owlpretty l
    owlpretty' _ (ParamTy t) = owlpretty t
    owlpretty' _ (ParamIdx i _) = owlpretty i
    owlpretty' _ (ParamName ne) = owlpretty ne

instance  OwlPretty Endpoint where
    owlpretty' _ (Endpoint  x) = owlpretty x
    owlpretty' _ (EndpointLocality l) = owlpretty "endpoint(" <> owlpretty l <> owlpretty ")"

instance  OwlPretty Locality where
    owlpretty' _ (Locality s xs) = owlpretty s <> angles (mconcat $ map owlpretty xs)

instance  OwlPretty DeclX where
    owlpretty' _ d = owlpretty (show d)

instance  OwlPretty ModuleExpX where
    owlpretty' b (ModuleBody _ nk) = 
        let (n, k) = owlprettyBind' b nk in
        angles (n <> owlpretty "." <> k)
    owlpretty' _ (ModuleVar p) = owlpretty p
    owlpretty' _ x = owlpretty $ show x

optext :: OwlPretty a => a -> T.Text
optext x = T.renderStrict $ layoutPretty defaultLayoutOptions $ owlpretty x
