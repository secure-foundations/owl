(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)

(declare-sort Bits)
(declare-fun B2I (Bits) Int)
(declare-fun I2B (Int) Bits)
(declare-fun OkInt (Bits) Bool)
(assert (forall ((x Int)) (!
    (OkInt (I2B x))
    :pattern (I2B x)
    :qid okint_i2b
)))

; HasHex b s is true when:
; - s is a valid hex string in ASCII; and
; - b is the bitvector corresponding to the hex string
(declare-fun HasHex (Bits String) Bool)
(assert (forall ((x Bits) (s1 String) (s2 String)) (!
    (=> (and (HasHex x s1) (HasHex x s2))
        (= s1 s2))
    :pattern ((HasHex x s1) (HasHex x s2))
    :qid hashex_unique
)))

(assert (forall ((x Int)) (!
    (=> (>= x 0)
        (= (B2I (I2B x)) x))
    :pattern (I2B x)
    :qid i2b_b2i
)))
(assert (forall ((x Bits)) (!
    (=> (OkInt x)
        (and 
            (= (I2B (B2I x)) x)
            (>= (B2I x) 0)))
    :pattern (B2I x)
    :qid b2i_i2b
)))

;; Built-in functions on bits
(declare-fun length (Bits) Bits)
(assert (forall ((x Bits)) (!
    (and 
        (>= (B2I (length x)) 0)
        (OkInt (length x)))
    :pattern (length x)
    :qid b2i_length
)))


(declare-fun concat (Bits Bits) Bits)
(declare-fun Prefix (Bits Int) Bits)
(declare-fun Postfix (Bits Int) Bits)
(assert (forall ((x Bits) (y Bits)) (!
    (= (Prefix (concat x y) (B2I (length x))) x)
    :pattern ((Prefix (concat x y) (B2I (length x))))
    :qid prefix_concat_length
)))

(assert (forall ((x Bits) (y Bits)) (!
    (= (Postfix (concat x y) (B2I (length x))) y)
    :pattern ((Postfix (concat x y) (B2I (length x))))
    :qid postfix_concat_length
)))

(assert (forall ((x Bits) (y Bits)) (!
    (= (length (concat x y)) (I2B (+ (B2I (length x)) (B2I (length y)))))
    :pattern ((length (concat x y)))
    :qid length_concat
)))

(assert (forall ((x Bits) (n Int)) (!
    (=> 
        (and (>= n 0 ) (>= (B2I (length x)) n))
        (= (concat (Prefix x n) (Postfix x n)) x))
    :pattern ((concat (Prefix x n) (Postfix x n)))
    :qid concat_prefix_postfix
)))

(assert (forall ((x Bits) (y Bits) (z Bits)) (!
    (= (concat (concat x y) z) (concat x (concat y z)))
    :pattern ((concat (concat x y) z))
    :qid concat_assoc
)))



(declare-fun eq (Bits Bits) Bits)
(declare-fun TRUE () Bits)
(declare-fun FALSE () Bits)
(assert (not (= TRUE FALSE)))
(assert (= (length TRUE) (I2B 1)))
(assert (= (length FALSE) (I2B 1)))
(assert (forall ((x Bits) (y Bits)) (!
    (= (eq x y) (ite (= x y) TRUE FALSE))
    :pattern (eq x y)
    :qid eq_def
)))
(assert (forall ((x Bits) (y Bits)) (!
    (=> (not (= (length x) (length y)))
        (not (= TRUE (eq x y))))
    :pattern ((eq x y))
    :qid eq_length_eq
)))
(declare-fun And (Bits Bits) Bits)
(assert (forall ((x Bits) (y Bits)) (!
    (= (And x y) 
       (ite (= x TRUE) (ite (= y TRUE) TRUE FALSE) FALSE))
    :pattern (And x y)
    :qid and_def
)))
(declare-fun UNIT () Bits)
(assert (= (length UNIT) (I2B 0)))

(assert (forall ((x Bits) (y Bits) (z Bits) (w Bits)) (!
    (=> (and (or (= TRUE (eq (length x) (length z))) (= TRUE (eq (length y) (length w))))
             (= TRUE (eq (concat x y) (concat z w))))
        (and (= TRUE (eq x z)) (= TRUE (eq y w))))
    :pattern ((eq (concat x y) (concat z w)))
    :qid eq_concat
)))

(declare-sort Type)
(declare-fun HasType (Bits Type) Bool)

(declare-const TBool Type)
(assert (forall ((x Bits)) (!
    (= (HasType x TBool) (or (= x TRUE) (= x FALSE)))
    :pattern (HasType x TBool)
    :qid hastype_tbool
)))

(declare-const Nat Type)
(assert (forall ((x Bits)) (!
    (= (HasType x Nat) (>= (B2I x) 0))
    :pattern (HasType x Nat)
    :qid hastype_nat
)))


(declare-fun Unit () Type)
(assert (forall ((x Bits)) (!
    (= (HasType x Unit) (= x UNIT))
    :pattern (HasType x Unit)
    :qid hastype_unit
)))

(declare-fun EnumTag (Int) Bits)
(assert (forall ((x Int)) (!
    (=> (and (>= x 0) (< x 256))
        (and (OkInt (EnumTag x)) 
             (= (B2I (length (EnumTag x))) 2)
             (= (B2I (EnumTag x)) x)))
    :pattern (EnumTag x)
    :qid enumtag_def
)))

(define-fun TestEnumTag ((x Int) (y Bits)) Bits
    (eq (Prefix y 2) (EnumTag x)))

(declare-sort Name)
(declare-fun ValueOf (Name) Bits)
(declare-fun TName (Name) Type)
(assert (forall ((x Bits) (n Name)) (!
    (= (HasType x (TName n))
        (= TRUE (eq x (ValueOf n))))
    :pattern (HasType x (TName n))
    :qid hastype_name
)))

(declare-const NonceLength Int)
(assert (>= NonceLength 32))

(declare-sort NameKind)
(declare-fun NameKindLength (NameKind) Int)
(declare-const Enckey NameKind)
(declare-fun Nonce (Int) NameKind)
(assert (forall ((i Int)) (!
    (= (NameKindLength (Nonce i)) i)
    :pattern (Nonce i)
    :qid nonce_length
)))
(declare-const Sigkey NameKind)
(declare-const DHkey NameKind)
(declare-const PKEkey NameKind)
(declare-const KDFkey NameKind)
(declare-const MACkey NameKind)
(declare-fun HasNameKind (Name NameKind) Bool)
(assert (forall ((n Name) (k NameKind)) (!
    (= (HasNameKind n k) (= (I2B (NameKindLength k)) (length (ValueOf n))))
    :pattern (HasNameKind n k)
    :qid hasnamekind_length
)))


(declare-const SignatureLen Int)
(assert (> SignatureLen 0))

(declare-const PKEPubLen Int)
(assert (> PKEPubLen 0))

(declare-const VKLen Int)
(assert (> VKLen 0))

(declare-const MAClen Int)
(assert (> MAClen 0))

(declare-const Taglen Int)
(assert (> Taglen 0))

(declare-const Counterlen Int)
(assert (> Counterlen 0))

(declare-const GroupLen Int)
(assert (> GroupLen 0))
(declare-fun dhpk (Bits) Bits)
(declare-fun IsExponent (Bits) Bool)
(declare-fun is_group_elem (Bits) Bits)
(assert (forall ((x Bits)) (!
    (=> (IsExponent x) (= (length x) (I2B (NameKindLength DHkey))))
    :pattern (IsExponent x)
    :qid is_exponent_length
)))

(assert (forall ((n Name)) (!
    (=> (HasNameKind n DHkey)
        (IsExponent (ValueOf n)))
    :pattern (HasNameKind n DHkey)
    :qid dhkey_isexponent
)))

(assert (forall ((x Bits)) (!
    (=> (= TRUE (is_group_elem x)) (= (length x) (I2B GroupLen)))
    :pattern (is_group_elem x)
    :qid is_group_elem_def
)))
(assert (forall ((x Bits)) (!
    (HasType (is_group_elem x) TBool)
    :pattern ((is_group_elem x) )
    :qid is_group_elem_bool
)))
(assert (forall ((x Bits)) (!
    (=> (IsExponent x) (= TRUE (is_group_elem (dhpk x))))
    :pattern (IsExponent x)
    :qid is_exponent_def
)))


(declare-fun dh_combine (Bits Bits) Bits)

(assert (forall ((x Bits) (y Bits)) (!
    (=> (and (IsExponent y) (= TRUE (is_group_elem x)))
        (= TRUE (is_group_elem (dh_combine x y))))
    :pattern (dh_combine x y)
    :qid is_group_elem_dh_combine
)))

(assert (forall ((x Bits) (y Bits)) (!
    (=> (and (IsExponent x) (IsExponent y))
        (= (dh_combine (dhpk x) y)
           (dh_combine (dhpk y) x)))
    :pattern (dh_combine (dhpk x) y)
    :qid dh_combine_comm
)))
(assert (forall ((x Bits) (y Bits) (z Bits)) (!
    (=> (and (IsExponent x) (IsExponent y) (= TRUE (is_group_elem z))
             (= TRUE (eq (dh_combine z x) (dh_combine z y))))
        (= TRUE (eq x y)))
    :pattern (eq (dh_combine z x) (dh_combine z y))
    :qid dh_combine_inj_1
)))

(assert (forall ((x Bits) (y Bits) (z Bits)) (!
    (=> (and (IsExponent x) (= TRUE (is_group_elem y)) (= TRUE (is_group_elem z))
             (= TRUE (eq (dh_combine y x) (dh_combine z x))))
        (= TRUE (eq y z)))
    :pattern (eq (dh_combine y x) (dh_combine z x))
    :qid dh_combine_inj_2
)))

(assert (forall ((x Bits) (y Bits)) (!
    (=>
        (and (IsExponent x) (IsExponent y)
             (= TRUE (eq (dhpk x) (dhpk y))))
        (= TRUE (eq x y)))
    :pattern ((eq (dhpk x) (dhpk y)))
    :qid dhpk_inj
 )))

(declare-fun xor (Bits Bits) Bits) ; concat and truncate to smaller
(assert (forall ((x Bits) (y Bits)) (!
    (= TRUE (eq (xor x y) (xor y x)))
    :pattern (xor x y)
    :qid xor_comm
)))

(assert (forall ((x Bits) (y Bits) (z Bits)) (!
    (=>
        (and 
            (= TRUE (eq (xor x y) (xor x z)))
            (= (length x) (length y))
            (= (length x) (length z)))
        (= TRUE (eq y z)))
    :pattern (eq (xor x y) (xor x z))
    :qid xor_cancel_l
)))

(assert (forall ((x Bits) (y Bits) (z Bits)) (!
    (=>
        (and 
            (= TRUE (eq (xor y x) (xor z x)))
            (= (length x) (length y))
            (= (length x) (length z)))
        (= TRUE (eq y z)))
    :pattern (eq (xor y x) (xor z x))
    :qid xor_cancel_r
)))


(declare-fun HonestPKEnc (Name Bits) Bool) ; Abstract predcate for if the PK
; encryption is honest or adversarial

(declare-fun IsConstant (Bits) Bool) ; The set of bits that names should never
; intersect. For soundness, this set must have measure zero

(declare-fun KDF (Bits Bits Bits Int Int) Bits)
(declare-fun KDFName (Bits Bits Bits Int Int) Name)

(assert (forall ((x Bits) (y Bits) (z Bits) (i Int) (j Int)) (!
    (=>
        (and (>= j 0) (>= i 0))
        (= (length (KDF x y z i j)) (I2B j)
    ))
    :pattern ((KDF x y z i j))
    :qid kdf_length
)))

; Abstract permission that the specified KDF hash has a certain name type
; (name type given by last argument counter)
(declare-fun KDFPerm (Bits Bits Bits Int Int Int) Bool)

(assert (forall ((n1 Name) (n2 Name)) (!
    (=> (= TRUE (eq (ValueOf n1) (ValueOf n2)))
        (= n1 n2))
    :pattern (eq (ValueOf n1) (ValueOf n2))
    :qid valueof_name_inj
)))

(assert (forall ((x Bits) (n Name)) (!
    (=> (IsConstant x)
        (not (= TRUE (eq x (ValueOf n)))))
    :pattern ((IsConstant x) (eq x (ValueOf n)))
    :qid isconstant_neq_name
)))

; The below can be generalized
(assert (forall ((a Bits) (x Bits) (y Bits) (n Name) (i Int) (j Int)) (!
    (=> (and 
            (HasNameKind n DHkey)
            (IsConstant a))
         (not (= TRUE (eq a (KDF x (dhpk (ValueOf n)) y i j)))))
    :pattern ((IsConstant a) (eq a (KDF x (dhpk (ValueOf n)) y i j)))
    :qid isconstant_neq_kdf_dhpk
)))


(declare-fun andb (Bits Bits) Bits)
(assert (forall ((x Bits) (y Bits)) (!
    (= (andb x y) (ite (= TRUE x) (ite (= TRUE y) TRUE FALSE) FALSE))
    :pattern (andb x y)
    :qid andb_def
)))

(define-fun zero () Bits (I2B 0))

(declare-fun plus (Bits Bits) Bits)
(assert (forall ((x Bits) (y Bits)) (!
    (= (plus x y) (I2B (+ (B2I x) (B2I y))))
    :pattern (plus x y)
    :qid plus_def
)))
(declare-fun mult (Bits Bits) Bits)
(assert (forall ((x Bits) (y Bits)) (!
    (= (mult x y) (I2B (* (B2I x) (B2I y))))
    :pattern (mult x y)
    :qid mult_def
)))

(assert (forall ((x Int) (y Bits)) (!
    (=> (>= x 0)
        (= (mult (I2B x) y)
           (I2B (* x (B2I y)))))
    :pattern (mult (I2B x) y)
    :qid mult_int_l
)))

(declare-fun crh (Bits) Bits)
(declare-fun CrhLength () Int)
(assert (> CrhLength 0))
(assert (forall ((x Bits)) (!
    (= (length (crh x)) (I2B CrhLength))
    :pattern (crh x)
    :qid crh_length
)))

(declare-sort Label)
(declare-const %adv Label)


(declare-fun Flows (Label Label) Bool)
; Below is to get pattern instantiation to work
(define-fun FlowsImpl ((x Label) (y Label)) Bool ((_ partial-order 0) x y))
(assert (forall ((x Label) (y Label)) (! 
    (= (Flows x y) (FlowsImpl x y))
    :pattern ((Flows x y))
    :qid flows_def
)))

(declare-fun Join (Label Label) Label)
(assert (forall ((x Label) (y Label)) (! 
    (Flows x (Join x y))
    :pattern ((Join x y))
    :qid flows_join_1
)))

(assert (forall ((x Label) (y Label)) (! 
    (Flows y (Join x y))
    :pattern ((Join x y))
    :qid flows_join_2
)))
(assert (forall ((x Label) (y Label) (z Label)) (! 
    (=> (and (Flows x z) (Flows y z)) (Flows (Join x y) z))
    :pattern ((Flows (Join x y) z))
    :qid flows_join_l
)))

(declare-const %zeroLbl Label)
(assert (forall ((x Label)) (! 
    (Flows %zeroLbl x)
    :pattern ((Flows %zeroLbl x))
    :qid flows_zero_l
)))

(assert (forall ((x Label)) (!
    (=> (Flows x %zeroLbl) (= x %zeroLbl))
    :pattern ((Flows x %zeroLbl))
    :qid flows_zero_r
)))

(assert (forall ((x Label)) (!
    (= (Join x %zeroLbl) x)
    :pattern ((Join x %zeroLbl))
    :qid join_zero_r
)))

(assert (forall ((x Label)) (!
    (= (Join %zeroLbl x) x)
    :pattern ((Join %zeroLbl x))
    :qid join_zero_l
)))

(declare-const %ghost Label)
(declare-const %top Label)
(assert (forall ((x Label)) (! 
    (Flows x %ghost)
    :pattern ((Flows x %ghost))
    :qid flows_ghost_l
)))

(assert (not (Flows %ghost %top)))

(assert (forall ((x Label)) (!
    (=> (Flows %ghost x) (= x %ghost))
    :pattern ((Flows %ghost x))
    :qid flows_ghost_r
)))

(declare-fun LabelOf (Name) Label)
(assert (forall ((n Name)) (!
    (not (Flows (LabelOf n) %zeroLbl))
    :pattern ((LabelOf n))
    :qid not_flows_name_zero
)))

(assert (forall ((n Name)) (!
    (Flows (LabelOf n) %top)
    :pattern ((LabelOf n))
    :qid flows_name_top
)))

(assert (Flows %adv %top))
(assert (Flows %zeroLbl %top))

(declare-sort Index)
(declare-fun Happened (String (List Index) (List Bits)) Bool)

;; Builtin function axioms
(assert (distinct TRUE FALSE UNIT))

(assert (forall ((n1 Name) (n2 Name) (n3 Name) (n4 Name)) (!
    (not (and (HasNameKind n1 DHkey) (HasNameKind n2 DHkey)
             (HasNameKind n3 DHkey) (HasNameKind n4 DHkey)
             (not (or (and (= n1 n3) (= n2 n4)) (and (= n1 n4) (= n2 n3))))
        (= TRUE (eq (dh_combine (dhpk (ValueOf n1)) (ValueOf n2))
                    (dh_combine (dhpk (ValueOf n3)) (ValueOf n4))))))
    :pattern (eq (dh_combine (dhpk (ValueOf n1)) (ValueOf n2))
                 (dh_combine (dhpk (ValueOf n3)) (ValueOf n4)))
    :qid dh_combine_neq_dh_combine
)))

(assert (forall ((n1 Name) (n2 Name) (n3 Name)) (!
    (not (and (HasNameKind n1 DHkey) (HasNameKind n2 DHkey) (HasNameKind n3 DHkey)
              (= TRUE (eq (dh_combine (dhpk (ValueOf n1)) (ValueOf n2)) (dhpk (ValueOf n3))))))
    :pattern ((eq (dh_combine (dhpk (ValueOf n1)) (ValueOf n2)) (dhpk (ValueOf n3))))
    :pattern dh_combine_neq_dhpk
)))


