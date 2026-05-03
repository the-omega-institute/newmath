import BEDC.Derived.FieldUp
import BEDC.Derived.FieldUp.SingletonContinuation
import BEDC.FKernel.Cont

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def FieldApartZero (a : BHist) : Prop :=
  hsame a BHist.Empty -> False

theorem FieldApartZero_empty_hsame_transport {a b : BHist} :
    hsame a b -> FieldApartZero a -> (hsame b BHist.Empty -> False) := by
  intro same apart bEmpty
  exact apart (hsame_trans same bEmpty)

theorem FieldApartZero_semanticNameCert :
    SemanticNameCert FieldApartZero FieldApartZero FieldApartZero hsame := by
  exact {
    core := {
      carrier_inhabited := Exists.intro (BHist.e0 BHist.Empty)
        (fun sameEmpty => not_hsame_e0_empty sameEmpty)
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same carrier kEmpty
        exact carrier (hsame_trans same kEmpty)
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

theorem FieldApartZero_append_left_context_semanticNameCert {p : BHist} :
    FieldApartZero p ->
      SemanticNameCert (fun q : BHist => FieldApartZero (append q p))
        (fun q : BHist => FieldApartZero (append q p))
        (fun q : BHist => FieldApartZero (append q p)) hsame := by
  intro apartP
  constructor
  · constructor
    · exact Exists.intro BHist.Empty
        (FieldApartZero_empty_hsame_transport (hsame_symm (append_empty_left p)) apartP)
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrierH
      cases same
      exact carrierH
  · intro h source
    exact source
  · intro h source
    exact source

theorem FieldApartZero_append_right_context_semanticNameCert {p : BHist} :
    FieldApartZero p ->
      SemanticNameCert (fun q : BHist => FieldApartZero (append p q))
        (fun q : BHist => FieldApartZero (append p q))
        (fun q : BHist => FieldApartZero (append p q)) hsame := by
  intro apartP
  constructor
  · constructor
    · exact Exists.intro BHist.Empty
        (FieldApartZero_empty_hsame_transport (hsame_symm (append_empty_right p)) apartP)
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrierH
      cases same
      exact carrierH
  · intro h source
    exact source
  · intro h source
    exact source

theorem FieldApartZero_append_context_semanticNameCert {L R : BHist} (apartL : FieldApartZero L) :
    SemanticNameCert (fun h : BHist => FieldApartZero (append L (append h R)))
      (fun h : BHist => FieldApartZero (append L (append h R)))
      (fun h : BHist => FieldApartZero (append L (append h R))) hsame := by
  constructor
  · constructor
    · exact Exists.intro BHist.Empty (by
        intro contextEmpty
        exact apartL (append_eq_empty_iff.mp contextEmpty).left)
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrierH
      cases same
      exact carrierH
  · intro h source
    exact source
  · intro h source
    exact source

theorem FieldApartZero_append_factor_closed {p q : BHist} :
    FieldApartZero p ∨ FieldApartZero q -> FieldApartZero (append p q) := by
  intro factorApart appendEmpty
  have splitEmpty := append_eq_empty_iff.mp appendEmpty
  cases factorApart with
  | inl leftApart =>
      exact leftApart splitEmpty.left
  | inr rightApart =>
      exact rightApart splitEmpty.right

theorem FieldApartZero_append_left_factor_of_tail_not_apart {p q : BHist} :
    FieldApartZero (append p q) -> (FieldApartZero q -> False) -> FieldApartZero p := by
  intro appendApart tailNotApart pEmpty
  have qEmpty : hsame q BHist.Empty := by
    cases q with
    | Empty =>
        exact hsame_refl BHist.Empty
    | e0 q =>
        exact False.elim (tailNotApart (fun qEmpty => not_hsame_e0_empty qEmpty))
    | e1 q =>
        exact False.elim (tailNotApart (fun qEmpty => not_hsame_e1_empty qEmpty))
  exact appendApart (append_eq_empty_iff.mpr (And.intro pEmpty qEmpty))

theorem FieldApartZero_append_split_iff {p q : BHist} :
    FieldApartZero (append p q) <-> FieldApartZero p ∨ FieldApartZero q := by
  constructor
  · intro appendApart
    cases p with
    | Empty =>
        right
        intro qEmpty
        exact appendApart (hsame_trans (append_empty_left q) qEmpty)
    | e0 p =>
        left
        intro pEmpty
        exact not_hsame_e0_empty pEmpty
    | e1 p =>
        left
        intro pEmpty
        exact not_hsame_e1_empty pEmpty
  · intro split
    exact FieldApartZero_append_factor_closed split

theorem FieldApartZero_continuation_endpoint_split_iff {p q r : BHist} :
    Cont p q r -> (FieldApartZero r <-> FieldApartZero p ∨ FieldApartZero q) := by
  intro continuation
  cases continuation
  constructor
  · intro appendApart
    cases p with
    | Empty =>
        right
        intro qEmpty
        exact appendApart (hsame_trans (append_empty_left q) qEmpty)
    | e0 p =>
        left
        intro pEmpty
        exact not_hsame_e0_empty pEmpty
    | e1 p =>
        left
        intro pEmpty
        exact not_hsame_e1_empty pEmpty
  · intro split appendEmpty
    have splitEmpty := append_eq_empty_iff.mp appendEmpty
    cases split with
    | inl leftApart =>
        exact leftApart splitEmpty.left
    | inr rightApart =>
        exact rightApart splitEmpty.right

theorem FieldApartZero_continuation_singleton_result_factor_absurd {P Q R endpoint : BHist} :
    Cont P Q R -> FieldSingletonClassifier R endpoint ->
      (FieldApartZero P -> False) ∧ (FieldApartZero Q -> False) := by
  intro continuation classified
  have endpoints :=
    (FieldSingletonCarrier_continuation_endpoint_split_iff continuation).mp classified.left
  constructor
  · intro apartP
    exact apartP endpoints.left
  · intro apartQ
    exact apartQ endpoints.right

theorem FieldApartZero_append_hsame_congr_iff {a a' b b' : BHist} :
    hsame a a' -> hsame b b' ->
      (FieldApartZero (append a b) <-> FieldApartZero (append a' b')) := by
  intro sameA sameB
  have sameAppend : hsame (append a b) (append a' b') := by
    cases sameA
    cases sameB
    exact hsame_refl (append a b)
  constructor
  · intro apart
    exact FieldApartZero_empty_hsame_transport sameAppend apart
  · intro apart
    exact FieldApartZero_empty_hsame_transport (hsame_symm sameAppend) apart

theorem FieldApartZero_append_right_empty_iff {p q : BHist}
    (qEmpty : hsame q BHist.Empty) :
    FieldApartZero (append p q) <-> FieldApartZero p := by
  constructor
  · intro appendApart pEmpty
    exact appendApart (append_eq_empty_iff.mpr (And.intro pEmpty qEmpty))
  · intro pApart appendEmpty
    exact pApart (append_eq_empty_iff.mp appendEmpty).left

theorem FieldApartZero_append_left_empty_iff {p q : BHist}
    (pEmpty : hsame p BHist.Empty) :
    FieldApartZero (append p q) <-> FieldApartZero q := by
  constructor
  · intro appendApart qEmpty
    exact appendApart (append_eq_empty_iff.mpr (And.intro pEmpty qEmpty))
  · intro qApart appendEmpty
    exact qApart (append_eq_empty_iff.mp appendEmpty).right

theorem FieldApartZero_append_visible_headed {p q : BHist} :
    FieldApartZero (append (BHist.e0 p) q) ∧
      FieldApartZero (append (BHist.e1 p) q) := by
  constructor
  · intro appendEmpty
    exact not_hsame_e0_empty (append_eq_empty_iff.mp appendEmpty).left
  · intro appendEmpty
    exact not_hsame_e1_empty (append_eq_empty_iff.mp appendEmpty).left

theorem FieldApartZero_nested_continuation_visible_left_result {tail h r u v : BHist} :
    (Cont (BHist.e0 tail) h u -> Cont u r v -> FieldApartZero v) ∧
      (Cont (BHist.e1 tail) h u -> Cont u r v -> FieldApartZero v) := by
  constructor
  · intro leftCont resultCont resultEmpty
    cases leftCont
    cases resultCont
    have outerEmpty := append_eq_empty_iff.mp resultEmpty
    have innerEmpty := append_eq_empty_iff.mp outerEmpty.left
    exact not_hsame_e0_empty innerEmpty.left
  · intro leftCont resultCont resultEmpty
    cases leftCont
    cases resultCont
    have outerEmpty := append_eq_empty_iff.mp resultEmpty
    have innerEmpty := append_eq_empty_iff.mp outerEmpty.left
    exact not_hsame_e1_empty innerEmpty.left

theorem FieldApartZero_empty_context_iff {l h r : BHist} :
    hsame l BHist.Empty -> hsame r BHist.Empty ->
      (FieldApartZero (append l (append h r)) <-> FieldApartZero h) := by
  intro leftEmpty rightEmpty
  constructor
  · intro contextApart hEmpty
    have innerEmpty : hsame (append h r) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro hEmpty rightEmpty)
    exact contextApart (append_eq_empty_iff.mpr (And.intro leftEmpty innerEmpty))
  · intro hApart contextEmpty
    have outerSplit := append_eq_empty_iff.mp contextEmpty
    have innerSplit := append_eq_empty_iff.mp outerSplit.right
    exact hApart innerSplit.left

theorem FieldApartZero_nested_continuation_factor_split_iff {l h r u v q w : BHist} :
    Cont l h u -> Cont u r v -> Cont v q w ->
      hsame l BHist.Empty -> hsame r BHist.Empty ->
        (FieldApartZero w <-> FieldApartZero h ∨ FieldApartZero q) := by
  intro leftContinuation rightContinuation tailContinuation leftEmpty rightEmpty
  cases leftContinuation
  cases rightContinuation
  cases tailContinuation
  have middleSame : hsame (append (append l h) r) h := by
    cases leftEmpty
    cases rightEmpty
    exact hsame_trans (append_empty_right (append BHist.Empty h)) (append_empty_left h)
  have resultIff :=
    FieldApartZero_append_hsame_congr_iff middleSame (hsame_refl q)
  constructor
  · intro apartResult
    exact Iff.mp FieldApartZero_append_split_iff (Iff.mp resultIff apartResult)
  · intro factorApart
    exact Iff.mpr resultIff (Iff.mpr FieldApartZero_append_split_iff factorApart)

theorem FieldApartZero_nested_continuation_empty_context_iff {l h r u v : BHist} :
    Cont l h u -> Cont u r v -> hsame l BHist.Empty -> hsame r BHist.Empty ->
      (FieldApartZero v <-> FieldApartZero h) := by
  intro leftCont rightCont leftEmpty rightEmpty
  cases leftCont
  cases rightCont
  have contextIff := FieldApartZero_empty_context_iff (l := l) (h := h) (r := r)
    leftEmpty rightEmpty
  constructor
  · intro nestedApart
    exact Iff.mp contextIff
      (FieldApartZero_empty_hsame_transport (append_assoc l h r) nestedApart)
  · intro coreApart
    exact FieldApartZero_empty_hsame_transport (hsame_symm (append_assoc l h r))
      (Iff.mpr contextIff coreApart)

theorem field_apartzero_inverse_involutive {mul : BHist -> BHist -> BHist} {one : BHist}
    {inv : (a : BHist) -> (hsame a BHist.Empty -> False) -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : hsame a BHist.Empty -> False),
      hsame (mul (inv a p) a) one)
    (inverseApart : forall (a : BHist) (p : hsame a BHist.Empty -> False),
      hsame (inv a p) BHist.Empty -> False)
    {a : BHist} (pa : hsame a BHist.Empty -> False) :
    hsame (inv (inv a pa) (inverseApart a pa)) a := by
  exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
    assocC leftId rightId mulCongr
    (leftInv (inv a pa) (inverseApart a pa))
    (leftInv a pa)

theorem field_product_apartness_inverse_product_reverse
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {inv : (a : BHist) -> FieldApartZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : FieldApartZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : FieldApartZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (pa : FieldApartZero a) (pb : FieldApartZero b) :
    Exists (fun pab : FieldApartZero (mul a b) =>
      hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa))) := by
  have productApart : FieldApartZero (mul a b) := by
    intro productEmpty
    have zeroCancel :=
      field_one_sided_zero_product_cancel_from_apartness
        (NonZero := FieldApartZero) (inv := inv) addAssoc zeroLeft negLeft
        assocC leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv a b
    exact pb (zeroCancel.left pa productEmpty)
  exact Exists.intro productApart
    (field_inverse_product_reverse_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv productApart pa pb)

theorem field_two_sided_product_apartzero_exact
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x : BHist} (pa : NonZero a) (pb : NonZero b) :
    FieldApartZero (mul (mul a x) b) <-> FieldApartZero x := by
  have productExact :
      hsame (mul (mul a x) b) BHist.Empty <-> hsame x BHist.Empty :=
    field_two_sided_empty_product_exact_from_apartness addAssoc zeroLeft negLeft
      assocC leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
      pa pb
  constructor
  · intro productApart
    intro xEmpty
    exact productApart (Iff.mpr productExact xEmpty)
  · intro xApart
    intro productEmpty
    exact xApart (Iff.mp productExact productEmpty)

theorem field_binary_product_apartzero_exact
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    (nonzeroEmptyAbsurd : NonZero BHist.Empty -> False)
    {a b : BHist} (alphaA : FieldApartZero a -> NonZero a)
    (alphaB : FieldApartZero b -> NonZero b) :
    FieldApartZero (mul a b) <-> FieldApartZero a ∧ FieldApartZero b := by
  have zeroAbsorption :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft
      addCongr mulCongr leftDistrib rightDistrib
  constructor
  · intro productApart
    constructor
    · intro aEmpty
      have productEmpty : hsame (mul a b) BHist.Empty := by
        exact hsame_trans (mulCongr aEmpty (hsame_refl b)) (zeroAbsorption.right b)
      exact productApart productEmpty
    · intro bEmpty
      have productEmpty : hsame (mul a b) BHist.Empty := by
        exact hsame_trans (mulCongr (hsame_refl a) bEmpty) (zeroAbsorption.left a)
      exact productApart productEmpty
  · intro factorsApart
    intro productEmpty
    exact field_nonzero_factors_exclude_empty_product addAssoc zeroLeft negLeft
      assocC leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
      nonzeroTransport nonzeroEmptyAbsurd (alphaA factorsApart.left)
      (alphaB factorsApart.right) productEmpty

theorem field_binary_product_apartzero_exact_from_apartness
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (apartToNonzero : forall {h : BHist}, (hsame h BHist.Empty -> False) -> NonZero h)
    {a b : BHist} :
    (hsame (mul a b) BHist.Empty -> False) <->
      (hsame a BHist.Empty -> False) /\ (hsame b BHist.Empty -> False) := by
  have zeroAbsorption :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft
      addCongr mulCongr leftDistrib rightDistrib
  constructor
  · intro productApart
    constructor
    · intro aEmpty
      have productEmpty : hsame (mul a b) BHist.Empty := by
        exact hsame_trans (mulCongr aEmpty (hsame_refl b)) (zeroAbsorption.right b)
      exact productApart productEmpty
    · intro bEmpty
      have productEmpty : hsame (mul a b) BHist.Empty := by
        exact hsame_trans (mulCongr (hsame_refl a) bEmpty) (zeroAbsorption.left a)
      exact productApart productEmpty
  · intro factorApart
    intro productEmpty
    have cancel :=
      field_one_sided_zero_product_cancel_from_apartness
        (NonZero := NonZero) (inv := inv) addAssoc zeroLeft negLeft assocC leftId rightId
        addCongr mulCongr leftDistrib rightDistrib leftInv rightInv a b
    exact factorApart.right (cancel.left (apartToNonzero factorApart.left) productEmpty)

protected theorem field_inverse_product_classifier_exact_from_apartness
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    (nonzeroEmptyAbsurd : NonZero BHist.Empty -> False)
    (apartToNonzero : forall {h : BHist}, (hsame h BHist.Empty -> False) -> NonZero h)
    {a b c d : BHist} (pa : NonZero a) (pb : NonZero b) (pc : NonZero c)
    (pd : NonZero d) :
    hsame (mul a b) (mul c d) <->
      hsame (mul (inv b pb) (inv a pa)) (mul (inv d pd) (inv c pc)) := by
  let pab : NonZero (mul a b) := apartToNonzero
    (field_nonzero_factors_exclude_empty_product addAssoc zeroLeft negLeft assocC
      leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
      nonzeroTransport nonzeroEmptyAbsurd pa pb)
  let pcd : NonZero (mul c d) := apartToNonzero
    (field_nonzero_factors_exclude_empty_product addAssoc zeroLeft negLeft assocC
      leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
      nonzeroTransport nonzeroEmptyAbsurd pc pd)
  have reverseAB :
      hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa)) :=
    field_inverse_product_reverse_from_apartness assocC leftId rightId mulCongr leftInv
      rightInv pab pa pb
  have reverseCD :
      hsame (inv (mul c d) pcd) (mul (inv d pd) (inv c pc)) :=
    field_inverse_product_reverse_from_apartness assocC leftId rightId mulCongr leftInv
      rightInv pcd pc pd
  constructor
  · intro sameProduct
    have sameInverseProducts :
        hsame (inv (mul a b) pab) (inv (mul c d) pcd) :=
      field_inverse_congruence_from_apartness assocC leftId rightId mulCongr leftInv
        rightInv sameProduct pab pcd
    exact hsame_trans (hsame_symm reverseAB)
      (hsame_trans sameInverseProducts reverseCD)
  · intro sameReverseProducts
    have sameInverseProducts :
        hsame (inv (mul a b) pab) (inv (mul c d) pcd) :=
      hsame_trans reverseAB (hsame_trans sameReverseProducts (hsame_symm reverseCD))
    exact field_inverse_cancel_from_apartness assocC leftId rightId mulCongr leftInv
      rightInv pab pcd sameInverseProducts

end BEDC.Derived.FieldUp
