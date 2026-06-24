import BEDC.Derived.RationalUp.Core

namespace BEDC.Derived.RationalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength bwordLength_append)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp

set_option linter.unusedSimpArgs false

private theorem nat_mul_assoc_clean (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

private theorem nat_right_distrib_clean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := Nat.mul_comm (a + b) c
    _ = c * a + c * b := Nat.left_distrib c a b
    _ = a * c + c * b := congrArg (fun x => x + c * b) (Nat.mul_comm c a)
    _ = a * c + b * c := congrArg (fun x => a * c + x) (Nat.mul_comm c b)

private theorem nat_mul_left_comm_clean (a b c : Nat) :
    a * (b * c) = b * (a * c) := by
  calc
    a * (b * c) = (a * b) * c := (nat_mul_assoc_clean a b c).symm
    _ = (b * a) * c := congrArg (fun t => t * c) (Nat.mul_comm a b)
    _ = b * (a * c) := nat_mul_assoc_clean b a c

private theorem nat_add_four_swap (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := Nat.add_assoc a b (c + d)
    _ = a + ((b + c) + d) := congrArg (fun t => a + t) (Nat.add_assoc b c d).symm
    _ = a + ((c + b) + d) := congrArg (fun t => a + (t + d)) (Nat.add_comm b c)
    _ = a + (c + (b + d)) := congrArg (fun t => a + t) (Nat.add_assoc c b d)
    _ = (a + c) + (b + d) := (Nat.add_assoc a c (b + d)).symm

private theorem nat_add_four_last_swap (a b c d : Nat) :
    (a + b) + (c + d) = (a + d) + (c + b) := by
  calc
    (a + b) + (c + d) = (a + b) + (d + c) :=
      congrArg (fun t => (a + b) + t) (Nat.add_comm c d)
    _ = (a + d) + (b + c) := nat_add_four_swap a b d c
    _ = (a + d) + (c + b) := congrArg (fun t => (a + d) + t) (Nat.add_comm b c)

private theorem nat_add_eight_assoc_perm (A B C D E F G H : Nat) :
    ((A + B) + (C + D)) + ((E + F) + (G + H)) =
      ((A + C) + (D + B)) + ((E + H) + (F + G)) := by
  calc
    ((A + B) + (C + D)) + ((E + F) + (G + H)) =
        ((A + C) + (B + D)) + ((E + F) + (G + H)) :=
      congrArg (fun t => t + ((E + F) + (G + H))) (nat_add_four_swap A B C D)
    _ = ((A + C) + (D + B)) + ((E + F) + (G + H)) :=
      congrArg (fun t => ((A + C) + t) + ((E + F) + (G + H))) (Nat.add_comm B D)
    _ = ((A + C) + (D + B)) + ((E + H) + (G + F)) :=
      congrArg (fun t => ((A + C) + (D + B)) + t) (nat_add_four_last_swap E F G H)
    _ = ((A + C) + (D + B)) + ((E + H) + (F + G)) :=
      congrArg (fun t => ((A + C) + (D + B)) + ((E + H) + t)) (Nat.add_comm G F)

private theorem nat_pair_mul_assoc_length_eq
    (a b c d e f : Nat) :
    ((a * b + c * d) * e + (a * d + c * b) * f) +
      (a * (b * f + d * e) + c * (b * e + d * f)) =
    (a * (b * e + d * f) + c * (b * f + d * e)) +
      ((a * b + c * d) * f + (a * d + c * b) * e) := by
  repeat rw [nat_right_distrib_clean]
  repeat rw [Nat.left_distrib]
  repeat rw [nat_mul_assoc_clean]
  exact nat_add_eight_assoc_perm
    (a * (b * e)) (c * (d * e)) (a * (d * f)) (c * (b * f))
    (a * (b * f)) (a * (d * e)) (c * (b * e)) (c * (d * f))

private theorem nat_pair_mul_add_distrib_length_eq
    (a b c d e f : Nat) :
    (a * (b + e) + c * (d + f)) +
      ((a * d + c * b) + (a * f + c * e)) =
    ((a * b + c * d) + (a * e + c * f)) +
      (a * (d + f) + c * (b + e)) := by
  repeat rw [Nat.left_distrib]
  exact (congrArg
    (fun t => t + ((a * d + c * b) + (a * f + c * e)))
    (nat_add_four_swap (a * b) (a * e) (c * d) (c * f))).trans
      (congrArg
        (fun t => ((a * b + c * d) + (a * e + c * f)) + t)
        (nat_add_four_swap (a * d) (c * b) (a * f) (c * e)))

def IntAdd (x y : IntegerUp) : IntegerUp :=
  intAdd x y

theorem intAdd_pair_classifier (x y : IntegerUp) :
    IntPairClassifier (intToPair (intAdd x y))
      (pairAdd (intToPair x) (intToPair y)) := by
  unfold intAdd
  exact intToPair_pairToInt_classifier _
    (pairAdd_carrier (intToPair_carrier x) (intToPair_carrier y))

theorem IntEq_refl (x : IntegerUp) : IntEq x x := by
  unfold IntEq
  exact IntPairClassifier_equivalence_fields.right.right.left (intToPair_carrier x)

theorem IntEq_symm {x y : IntegerUp} : IntEq x y -> IntEq y x := by
  intro same
  unfold IntEq at same ⊢
  exact IntPairClassifier_equivalence_fields.right.right.right.left same

theorem IntEq_trans {x y z : IntegerUp} : IntEq x y -> IntEq y z -> IntEq x z := by
  intro xy yz
  unfold IntEq at xy yz ⊢
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left xy yz

theorem pairAdd_pos_length (x y : BHist × BHist)
    (_hx : IntPairCarrier x.1 x.2) (_hy : IntPairCarrier y.1 y.2) :
    bwordLength (pairAdd x y).1 =
      bwordLength x.1 + bwordLength y.1 := by
  cases x with
  | mk xp xn =>
      cases y with
      | mk yp yn =>
          unfold pairAdd
          exact bwordLength_append xp yp

theorem pairAdd_neg_length (x y : BHist × BHist)
    (_hx : IntPairCarrier x.1 x.2) (_hy : IntPairCarrier y.1 y.2) :
    bwordLength (pairAdd x y).2 =
      bwordLength x.2 + bwordLength y.2 := by
  cases x with
  | mk xp xn =>
      cases y with
      | mk yp yn =>
          unfold pairAdd
          exact bwordLength_append xn yn

theorem pairMul_pos_length (x y : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2) (hy : IntPairCarrier y.1 y.2) :
    bwordLength (pairMul x y).1 =
      bwordLength x.1 * bwordLength y.1 +
        bwordLength x.2 * bwordLength y.2 := by
  cases x with
  | mk xp xn =>
      cases y with
      | mk yp yn =>
          unfold pairMul
          rw [bwordLength_append]
          rw [natMulFn_bwordLength hx.left hy.left]
          rw [natMulFn_bwordLength hx.right hy.right]

theorem pairMul_neg_length (x y : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2) (hy : IntPairCarrier y.1 y.2) :
    bwordLength (pairMul x y).2 =
      bwordLength x.1 * bwordLength y.2 +
        bwordLength x.2 * bwordLength y.1 := by
  cases x with
  | mk xp xn =>
      cases y with
      | mk yp yn =>
          unfold pairMul
          rw [bwordLength_append]
          rw [natMulFn_bwordLength hx.left hy.right]
          rw [natMulFn_bwordLength hx.right hy.left]

private theorem nat_pair_add_context_eq
    {xp xn x'p x'n yp yn y'p y'n : Nat}
    (hx : xp + x'n = x'p + xn)
    (hy : yp + y'n = y'p + yn) :
    (xp + yp) + (x'n + y'n) =
      (x'p + y'p) + (xn + yn) := by
  have left :
      (xp + x'n) + (yp + y'n) =
        (x'p + xn) + (yp + y'n) :=
    congrArg (fun t => t + (yp + y'n)) hx
  have right :
      (x'p + xn) + (yp + y'n) =
        (x'p + xn) + (y'p + yn) :=
    congrArg (fun t => (x'p + xn) + t) hy
  calc
    (xp + yp) + (x'n + y'n) = (xp + x'n) + (yp + y'n) :=
      nat_add_four_swap xp yp x'n y'n
    _ = (x'p + xn) + (yp + y'n) := congrArg (fun t => t + (yp + y'n)) hx
    _ = (x'p + xn) + (y'p + yn) := congrArg (fun t => (x'p + xn) + t) hy
    _ = (x'p + y'p) + (xn + yn) := (nat_add_four_swap x'p y'p xn yn).symm

private theorem nat_pair_mul_right_context_eq
    {p n q m r s : Nat}
    (h : p + m = q + n) :
    (p * r + n * s) + (q * s + m * r) =
      (q * r + m * s) + (p * s + n * r) := by
  have hR : p * r + m * r = q * r + n * r := by
    calc
      p * r + m * r = (p + m) * r := (nat_right_distrib_clean p m r).symm
      _ = (q + n) * r := congrArg (fun t => t * r) h
      _ = q * r + n * r := nat_right_distrib_clean q n r
  have hS : q * s + n * s = p * s + m * s := by
    calc
      q * s + n * s = (q + n) * s := (nat_right_distrib_clean q n s).symm
      _ = (p + m) * s := congrArg (fun t => t * s) h.symm
      _ = p * s + m * s := nat_right_distrib_clean p m s
  have sumEq :
      (p * r + m * r) + (q * s + n * s) =
        (q * r + n * r) + (p * s + m * s) :=
    (congrArg (fun t => t + (q * s + n * s)) hR).trans
      (congrArg (fun t => (q * r + n * r) + t) hS)
  calc
    (p * r + n * s) + (q * s + m * r) =
        (p * r + m * r) + (q * s + n * s) :=
      nat_add_four_last_swap (p * r) (n * s) (q * s) (m * r)
    _ = (q * r + n * r) + (p * s + m * s) := sumEq
    _ = (q * r + m * s) + (p * s + n * r) :=
      nat_add_four_last_swap (q * r) (n * r) (p * s) (m * s)

theorem pairAdd_classifier_congr {x x' y y' : BHist × BHist} :
    IntPairClassifier x x' -> IntPairClassifier y y' ->
      IntPairClassifier (pairAdd x y) (pairAdd x' y') := by
  intro xx' yy'
  apply IntPairClassifier_of_length_eq
    (pairAdd_carrier xx'.left yy'.left)
    (pairAdd_carrier xx'.right.left yy'.right.left)
  rw [pairAdd_pos_length x y xx'.left yy'.left]
  rw [pairAdd_neg_length x' y' xx'.right.left yy'.right.left]
  rw [pairAdd_pos_length x' y' xx'.right.left yy'.right.left]
  rw [pairAdd_neg_length x y xx'.left yy'.left]
  exact nat_pair_add_context_eq
    (IntPairClassifier_length_eq xx')
    (IntPairClassifier_length_eq yy')

theorem pairMul_right_classifier_congr {x x' y : BHist × BHist} :
    IntPairClassifier x x' -> IntPairCarrier y.1 y.2 ->
      IntPairClassifier (pairMul x y) (pairMul x' y) := by
  intro xx' hy
  apply IntPairClassifier_of_length_eq
    (pairMul_carrier xx'.left hy)
    (pairMul_carrier xx'.right.left hy)
  rw [pairMul_pos_length x y xx'.left hy]
  rw [pairMul_neg_length x' y xx'.right.left hy]
  rw [pairMul_pos_length x' y xx'.right.left hy]
  rw [pairMul_neg_length x y xx'.left hy]
  exact nat_pair_mul_right_context_eq (IntPairClassifier_length_eq xx')

theorem pairMul_left_classifier_congr {x y y' : BHist × BHist} :
    IntPairCarrier x.1 x.2 -> IntPairClassifier y y' ->
      IntPairClassifier (pairMul x y) (pairMul x y') := by
  intro hx yy'
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left
    (pairMul_comm x y hx yy'.left)
    (IntPairClassifier_equivalence_fields.right.right.right.right.left
      (pairMul_right_classifier_congr yy' hx)
      (IntPairClassifier_equivalence_fields.right.right.right.left
        (pairMul_comm x y' hx yy'.right.left)))

theorem pairMul_classifier_congr {x x' y y' : BHist × BHist} :
    IntPairClassifier x x' -> IntPairClassifier y y' ->
      IntPairClassifier (pairMul x y) (pairMul x' y') := by
  intro xx' yy'
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left
    (pairMul_right_classifier_congr xx' yy'.left)
    (pairMul_left_classifier_congr xx'.right.left yy')

theorem pairMul_unit_right (x : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2) :
    IntPairClassifier (pairMul x (NatOne, BHist.Empty)) x := by
  apply IntPairClassifier_of_length_eq
    (pairMul_carrier hx ⟨unary_e1_closed unary_empty, unary_empty⟩) hx
  rw [pairMul_pos_length x (NatOne, BHist.Empty) hx
    ⟨unary_e1_closed unary_empty, unary_empty⟩]
  rw [pairMul_neg_length x (NatOne, BHist.Empty) hx
    ⟨unary_e1_closed unary_empty, unary_empty⟩]
  rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
  rw [NatUp_unary_standard_bridge.left]
  rw [Nat.mul_one]
  rw [Nat.mul_zero]
  rw [Nat.mul_zero]
  rw [Nat.mul_one]
  rw [Nat.zero_add]
  rw [Nat.add_zero]

theorem pairMul_unit_left (x : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2) :
    IntPairClassifier (pairMul (NatOne, BHist.Empty) x) x :=
  IntPairClassifier_equivalence_fields.right.right.right.right.left
    (pairMul_comm (NatOne, BHist.Empty) x
      ⟨unary_e1_closed unary_empty, unary_empty⟩ hx)
    (pairMul_unit_right x hx)

theorem intMul_one_right (a : IntegerUp) :
    IntEq (IntMul a intOne) a := by
  unfold IntEq IntMul intOne intOfNat
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left
    (intMul_pair_classifier a
      { sign := BEDC.FKernel.Mark.BMark.b0,
        magnitude := NatOne,
        carrier := ⟨Or.inl rfl, unary_e1_closed unary_empty⟩ })
    (pairMul_unit_right (intToPair a) (intToPair_carrier a))

theorem intMul_one_left (a : IntegerUp) :
    IntEq (IntMul intOne a) a := by
  exact IntEq_trans (IntMul_comm intOne a) (intMul_one_right a)

theorem pairMul_same_sign_nat (s : BMark) (a b : BHist)
    (ha : UnaryHistory a) (hb : UnaryHistory b) :
    IntPairClassifier
      (pairMul (intToPair (intOfNatWithSign s a ha))
        (intToPair (intOfNatWithSign s b hb)))
      (natMulFn a b, BHist.Empty) := by
  cases s
  · apply IntPairClassifier_of_length_eq
      (pairMul_carrier (intToPair_carrier (intOfNatWithSign BMark.b0 a ha))
        (intToPair_carrier (intOfNatWithSign BMark.b0 b hb)))
      ⟨natMulFn_unary ha hb, unary_empty⟩
    change bwordLength (pairMul (a, BHist.Empty) (b, BHist.Empty)).1 +
        bwordLength BHist.Empty =
      bwordLength (natMulFn a b) +
        bwordLength (pairMul (a, BHist.Empty) (b, BHist.Empty)).2
    rw [pairMul_pos_length (a, BHist.Empty) (b, BHist.Empty)
      ⟨ha, unary_empty⟩ ⟨hb, unary_empty⟩]
    rw [pairMul_neg_length (a, BHist.Empty) (b, BHist.Empty)
      ⟨ha, unary_empty⟩ ⟨hb, unary_empty⟩]
    rw [natMulFn_bwordLength ha hb]
    change bwordLength a * bwordLength b +
        bwordLength BHist.Empty * bwordLength BHist.Empty +
        bwordLength BHist.Empty =
      bwordLength a * bwordLength b +
        (bwordLength a * bwordLength BHist.Empty +
          bwordLength BHist.Empty * bwordLength b)
    rw [NatUp_unary_standard_bridge.left]
    rw [Nat.mul_zero]
    rw [Nat.mul_zero]
    rw [Nat.zero_mul]
  · apply IntPairClassifier_of_length_eq
      (pairMul_carrier (intToPair_carrier (intOfNatWithSign BMark.b1 a ha))
        (intToPair_carrier (intOfNatWithSign BMark.b1 b hb)))
      ⟨natMulFn_unary ha hb, unary_empty⟩
    change bwordLength (pairMul (BHist.Empty, a) (BHist.Empty, b)).1 +
        bwordLength BHist.Empty =
      bwordLength (natMulFn a b) +
        bwordLength (pairMul (BHist.Empty, a) (BHist.Empty, b)).2
    rw [pairMul_pos_length (BHist.Empty, a) (BHist.Empty, b)
      ⟨unary_empty, ha⟩ ⟨unary_empty, hb⟩]
    rw [pairMul_neg_length (BHist.Empty, a) (BHist.Empty, b)
      ⟨unary_empty, ha⟩ ⟨unary_empty, hb⟩]
    rw [natMulFn_bwordLength ha hb]
    change bwordLength BHist.Empty * bwordLength BHist.Empty +
        bwordLength a * bwordLength b +
        bwordLength BHist.Empty =
      bwordLength a * bwordLength b +
        (bwordLength BHist.Empty * bwordLength b +
          bwordLength a * bwordLength BHist.Empty)
    rw [NatUp_unary_standard_bridge.left]
    rw [Nat.zero_mul]
    rw [Nat.mul_zero]
    rw [Nat.zero_mul]
    rw [Nat.zero_add]

theorem intMul_same_sign_nat (s : BMark) (a b : BHist)
    (ha : UnaryHistory a) (hb : UnaryHistory b) :
    IntEq (IntMul (intOfNatWithSign s a ha) (intOfNatWithSign s b hb))
      (intOfNat (natMulFn a b) (natMulFn_unary ha hb)) := by
  unfold IntEq IntMul intOfNat
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left
    (intMul_pair_classifier (intOfNatWithSign s a ha) (intOfNatWithSign s b hb))
    (pairMul_same_sign_nat s a b ha hb)

theorem pairMul_assoc (x y z : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2)
    (hy : IntPairCarrier y.1 y.2)
    (hz : IntPairCarrier z.1 z.2) :
    IntPairClassifier (pairMul (pairMul x y) z)
      (pairMul x (pairMul y z)) := by
  apply IntPairClassifier_of_length_eq
    (pairMul_carrier (pairMul_carrier hx hy) hz)
    (pairMul_carrier hx (pairMul_carrier hy hz))
  rw [pairMul_pos_length (pairMul x y) z (pairMul_carrier hx hy) hz]
  rw [pairMul_neg_length (pairMul x y) z (pairMul_carrier hx hy) hz]
  rw [pairMul_pos_length x y hx hy]
  rw [pairMul_neg_length x y hx hy]
  rw [pairMul_pos_length x (pairMul y z) hx (pairMul_carrier hy hz)]
  rw [pairMul_neg_length x (pairMul y z) hx (pairMul_carrier hy hz)]
  rw [pairMul_pos_length y z hy hz]
  rw [pairMul_neg_length y z hy hz]
  exact nat_pair_mul_assoc_length_eq
    (bwordLength x.1) (bwordLength y.1) (bwordLength x.2)
    (bwordLength y.2) (bwordLength z.1) (bwordLength z.2)

theorem intMul_assoc (a b c : IntegerUp) :
    IntEq (IntMul (IntMul a b) c) (IntMul a (IntMul b c)) := by
  unfold IntEq IntMul
  have leftOuter := intMul_pair_classifier (intMul a b) c
  have leftInner := intMul_pair_classifier a b
  have leftTransport :
      IntPairClassifier
        (pairMul (intToPair (intMul a b)) (intToPair c))
        (pairMul (pairMul (intToPair a) (intToPair b)) (intToPair c)) :=
    pairMul_right_classifier_congr leftInner (intToPair_carrier c)
  have assocPair :
      IntPairClassifier
        (pairMul (pairMul (intToPair a) (intToPair b)) (intToPair c))
        (pairMul (intToPair a) (pairMul (intToPair b) (intToPair c))) :=
    pairMul_assoc (intToPair a) (intToPair b) (intToPair c)
      (intToPair_carrier a) (intToPair_carrier b) (intToPair_carrier c)
  have rightInner := intMul_pair_classifier b c
  have rightTransport :
      IntPairClassifier
        (pairMul (intToPair a) (pairMul (intToPair b) (intToPair c)))
        (pairMul (intToPair a) (intToPair (intMul b c))) :=
    pairMul_left_classifier_congr (intToPair_carrier a)
      (IntPairClassifier_equivalence_fields.right.right.right.left rightInner)
  have rightOuter := intMul_pair_classifier a (intMul b c)
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left leftOuter
    (IntPairClassifier_equivalence_fields.right.right.right.right.left leftTransport
      (IntPairClassifier_equivalence_fields.right.right.right.right.left assocPair
        (IntPairClassifier_equivalence_fields.right.right.right.right.left rightTransport
          (IntPairClassifier_equivalence_fields.right.right.right.left rightOuter))))

theorem intMul_right_congr {a b c : IntegerUp} :
    IntEq a b -> IntEq (IntMul a c) (IntMul b c) := by
  intro same
  unfold IntEq at same
  unfold IntEq IntMul
  have leftOuter := intMul_pair_classifier a c
  have transport :
      IntPairClassifier
        (pairMul (intToPair a) (intToPair c))
        (pairMul (intToPair b) (intToPair c)) :=
    pairMul_right_classifier_congr same (intToPair_carrier c)
  have rightOuter := intMul_pair_classifier b c
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left leftOuter
    (IntPairClassifier_equivalence_fields.right.right.right.right.left transport
      (IntPairClassifier_equivalence_fields.right.right.right.left rightOuter))

theorem intMul_left_congr {a b c : IntegerUp} :
    IntEq a b -> IntEq (IntMul c a) (IntMul c b) := by
  intro same
  unfold IntEq at same
  unfold IntEq IntMul
  have leftOuter := intMul_pair_classifier c a
  have transport :
      IntPairClassifier
        (pairMul (intToPair c) (intToPair a))
        (pairMul (intToPair c) (intToPair b)) :=
    pairMul_left_classifier_congr (intToPair_carrier c) same
  have rightOuter := intMul_pair_classifier c b
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left leftOuter
    (IntPairClassifier_equivalence_fields.right.right.right.right.left transport
      (IntPairClassifier_equivalence_fields.right.right.right.left rightOuter))

theorem intMul_rotate_left (a b c : IntegerUp) :
    IntEq (IntMul a (IntMul b c)) (IntMul (IntMul b a) c) := by
  exact IntEq_trans (IntEq_symm (intMul_assoc a b c))
    (intMul_right_congr (IntMul_comm a b))

theorem intMul_middle_swap (a b c : IntegerUp) :
    IntEq (IntMul (IntMul a b) c) (IntMul (IntMul a c) b) := by
  exact IntEq_trans (intMul_assoc a b c)
    (IntEq_trans (intMul_left_congr (c := a) (IntMul_comm b c))
      (IntEq_symm (intMul_assoc a c b)))

theorem pairMul_add_distrib (x y z : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2)
    (hy : IntPairCarrier y.1 y.2)
    (hz : IntPairCarrier z.1 z.2) :
    IntPairClassifier (pairMul x (pairAdd y z))
      (pairAdd (pairMul x y) (pairMul x z)) := by
  apply IntPairClassifier_of_length_eq
    (pairMul_carrier hx (pairAdd_carrier hy hz))
    (pairAdd_carrier (pairMul_carrier hx hy) (pairMul_carrier hx hz))
  rw [pairMul_pos_length x (pairAdd y z) hx (pairAdd_carrier hy hz)]
  rw [pairMul_neg_length x (pairAdd y z) hx (pairAdd_carrier hy hz)]
  rw [pairAdd_pos_length y z hy hz]
  rw [pairAdd_neg_length y z hy hz]
  rw [pairAdd_pos_length (pairMul x y) (pairMul x z)
    (pairMul_carrier hx hy) (pairMul_carrier hx hz)]
  rw [pairAdd_neg_length (pairMul x y) (pairMul x z)
    (pairMul_carrier hx hy) (pairMul_carrier hx hz)]
  rw [pairMul_pos_length x y hx hy]
  rw [pairMul_neg_length x y hx hy]
  rw [pairMul_pos_length x z hx hz]
  rw [pairMul_neg_length x z hx hz]
  exact nat_pair_mul_add_distrib_length_eq
    (bwordLength x.1) (bwordLength y.1) (bwordLength x.2)
    (bwordLength y.2) (bwordLength z.1) (bwordLength z.2)

theorem intMul_add_distrib (a b c : IntegerUp) :
    IntEq (IntMul a (IntAdd b c))
      (IntAdd (IntMul a b) (IntMul a c)) := by
  unfold IntEq IntMul IntAdd
  have leftOuter := intMul_pair_classifier a (intAdd b c)
  have addInner := intAdd_pair_classifier b c
  have leftTransport :
      IntPairClassifier
        (pairMul (intToPair a) (intToPair (intAdd b c)))
        (pairMul (intToPair a) (pairAdd (intToPair b) (intToPair c))) :=
    pairMul_left_classifier_congr (intToPair_carrier a) addInner
  have distribPair :
      IntPairClassifier
        (pairMul (intToPair a) (pairAdd (intToPair b) (intToPair c)))
        (pairAdd (pairMul (intToPair a) (intToPair b))
          (pairMul (intToPair a) (intToPair c))) :=
    pairMul_add_distrib (intToPair a) (intToPair b) (intToPair c)
      (intToPair_carrier a) (intToPair_carrier b) (intToPair_carrier c)
  have leftMul := intMul_pair_classifier a b
  have rightMul := intMul_pair_classifier a c
  have addTransport :
      IntPairClassifier
        (pairAdd (pairMul (intToPair a) (intToPair b))
          (pairMul (intToPair a) (intToPair c)))
        (pairAdd (intToPair (intMul a b)) (intToPair (intMul a c))) :=
    pairAdd_classifier_congr
      (IntPairClassifier_equivalence_fields.right.right.right.left leftMul)
      (IntPairClassifier_equivalence_fields.right.right.right.left rightMul)
  have rightOuter := intAdd_pair_classifier (intMul a b) (intMul a c)
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left leftOuter
    (IntPairClassifier_equivalence_fields.right.right.right.right.left leftTransport
      (IntPairClassifier_equivalence_fields.right.right.right.right.left distribPair
        (IntPairClassifier_equivalence_fields.right.right.right.right.left addTransport
          (IntPairClassifier_equivalence_fields.right.right.right.left rightOuter))))

end BEDC.Derived.RationalUp
