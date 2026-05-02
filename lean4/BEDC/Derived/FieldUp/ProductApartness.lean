import BEDC.Derived.FieldUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def FieldApartZero (a : BHist) : Prop :=
  hsame a BHist.Empty -> False

theorem FieldApartZero_append_factor_closed {p q : BHist} :
    FieldApartZero p ∨ FieldApartZero q -> FieldApartZero (append p q) := by
  intro factorApart appendEmpty
  have splitEmpty := append_eq_empty_iff.mp appendEmpty
  cases factorApart with
  | inl leftApart =>
      exact leftApart splitEmpty.left
  | inr rightApart =>
      exact rightApart splitEmpty.right

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

end BEDC.Derived.FieldUp
