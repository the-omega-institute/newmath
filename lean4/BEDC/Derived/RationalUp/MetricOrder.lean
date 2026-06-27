import BEDC.Derived.RationalUp.FieldLaws
import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.RationalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (pairLe intLt natLeBool pairLe_of_length_order
  pairLe_total pairLe_antisymm_classifier intLt_to_pairLe pairLe_iff_length_order
  IntPairCarrier IntPairClassifier IntPairClassifier_equivalence_fields
  pairAdd pairNeg pairAdd_carrier pairNeg_carrier
  pairMul pairMul_carrier)

def ratSub (x y : RatNum) : RatNum :=
  ratAdd x (ratNeg y)

abbrev RatInt : Type :=
  BEDC.Derived.PrimeUp.IntegerUp

def intLe (x y : RatInt) : Prop :=
  pairLe (intToPair x) (intToPair y)

def intLtUp (x y : RatInt) : Prop :=
  intLt (intToPair x) (intToPair y)

def ratLe (x y : RatNum) : Prop :=
  intLe
    (IntMul x.num (ratDenInt y))
    (IntMul y.num (ratDenInt x))

def ratLt (x y : RatNum) : Prop :=
  intLtUp
    (IntMul x.num (ratDenInt y))
    (IntMul y.num (ratDenInt x))

def ratLeBool (x y : RatNum) : Bool :=
  natLeBool
    (bwordLength
        (intToPair (IntMul x.num (ratDenInt y))).1 +
      bwordLength
        (intToPair (IntMul y.num (ratDenInt x))).2)
    (bwordLength
        (intToPair (IntMul y.num (ratDenInt x))).1 +
      bwordLength
        (intToPair (IntMul x.num (ratDenInt y))).2)

def ratLtBool (x y : RatNum) : Bool :=
  natLeBool
    (Nat.succ
      (bwordLength
          (intToPair (IntMul x.num (ratDenInt y))).1 +
        bwordLength
          (intToPair (IntMul y.num (ratDenInt x))).2))
    (bwordLength
        (intToPair (IntMul y.num (ratDenInt x))).1 +
      bwordLength
        (intToPair (IntMul x.num (ratDenInt y))).2)

def ratAbs (x : RatNum) : RatNum :=
  ratMagnitude x

def ratDist (x y : RatNum) : RatNum :=
  ratAbs (ratSub x y)

theorem intLe_refl (x : RatInt) :
    intLe x x := by
  unfold intLe
  exact pairLe_of_length_order (intToPair_carrier x) (intToPair_carrier x)
    (Nat.le_refl _)

theorem intLe_total (x y : RatInt) :
    intLe x y ∨ intLe y x := by
  unfold intLe
  exact pairLe_total (intToPair_carrier x) (intToPair_carrier y)

theorem intLe_antisymm {x y : RatInt} :
    intLe x y -> intLe y x -> IntEq x y := by
  intro xy yx
  unfold intLe at xy yx
  unfold IntEq
  exact pairLe_antisymm_classifier (intToPair_carrier x) (intToPair_carrier y) xy yx

private theorem nat_add_four_last_swap (a b c d : Nat) :
    (a + b) + (c + d) = (a + d) + (c + b) := by
  calc
    (a + b) + (c + d) = (a + b) + (d + c) :=
      congrArg (fun t => (a + b) + t) (Nat.add_comm c d)
    _ = a + (b + (d + c)) := Nat.add_assoc a b (d + c)
    _ = a + ((b + d) + c) := congrArg (fun t => a + t) (Nat.add_assoc b d c).symm
    _ = a + ((d + b) + c) := congrArg (fun t => a + (t + c)) (Nat.add_comm b d)
    _ = a + (d + (b + c)) := congrArg (fun t => a + t) (Nat.add_assoc d b c)
    _ = (a + d) + (b + c) := (Nat.add_assoc a d (b + c)).symm
    _ = (a + d) + (c + b) := congrArg (fun t => (a + d) + t) (Nat.add_comm b c)

private theorem nat_add_four_swap (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := Nat.add_assoc a b (c + d)
    _ = a + ((b + c) + d) := congrArg (fun t => a + t) (Nat.add_assoc b c d).symm
    _ = a + ((c + b) + d) := congrArg (fun t => a + (t + d)) (Nat.add_comm b c)
    _ = a + (c + (b + d)) := congrArg (fun t => a + t) (Nat.add_assoc c b d)
    _ = (a + c) + (b + d) := (Nat.add_assoc a c (b + d)).symm

private theorem nat_le_cancel_add_right {a b c : Nat} :
    a + c ≤ b + c -> a ≤ b := by
  induction c with
  | zero =>
      intro h
      rw [Nat.add_zero] at h
      rw [Nat.add_zero] at h
      exact h
  | succ c ih =>
      intro h
      rw [Nat.add_succ] at h
      rw [Nat.add_succ] at h
      exact ih (Nat.le_of_succ_le_succ h)

private theorem nat_le_pair_transport {p n q m p' n' q' m' : Nat} :
    p + n' = p' + n ->
      q + m' = q' + m ->
        p + m ≤ q + n ->
          p' + m' ≤ q' + n' := by
  intro sameLeft sameRight le
  apply nat_le_cancel_add_right (c := n + q)
  calc
    (p' + m') + (n + q)
        = (p' + n) + (m' + q) :=
          nat_add_four_swap p' m' n q
    _ = (p + n') + (q' + m) := by
          have rightPart : m' + q = q' + m := by
            calc
              m' + q = q + m' := Nat.add_comm m' q
              _ = q' + m := sameRight
          rw [sameLeft.symm, rightPart]
    _ = (p + m) + (q' + n') :=
          nat_add_four_last_swap p n' q' m
    _ ≤ (q + n) + (q' + n') :=
          Nat.add_le_add_right le (q' + n')
    _ = (q' + n') + (n + q) := by
          calc
            (q + n) + (q' + n') =
                (n + q) + (q' + n') := by
                  rw [Nat.add_comm q n]
            _ = (q' + n') + (n + q) := Nat.add_comm (n + q) (q' + n')

theorem intLe_trans {x y z : RatInt} :
    intLe x y -> intLe y z -> intLe x z := by
  intro xy yz
  unfold intLe at xy yz ⊢
  have hx := intToPair_carrier x
  have hy := intToPair_carrier y
  have hz := intToPair_carrier z
  have xyLen := (pairLe_iff_length_order hx hy).mp xy
  have yzLen := (pairLe_iff_length_order hy hz).mp yz
  apply pairLe_of_length_order hx hz
  have combined :
      (bwordLength (intToPair x).1 + bwordLength (intToPair y).2) +
          (bwordLength (intToPair y).1 + bwordLength (intToPair z).2) ≤
        (bwordLength (intToPair y).1 + bwordLength (intToPair x).2) +
          (bwordLength (intToPair z).1 + bwordLength (intToPair y).2) :=
    Nat.add_le_add xyLen yzLen
  have rearranged :
      (bwordLength (intToPair x).1 + bwordLength (intToPair z).2) +
          (bwordLength (intToPair y).1 + bwordLength (intToPair y).2) ≤
        (bwordLength (intToPair z).1 + bwordLength (intToPair x).2) +
          (bwordLength (intToPair y).1 + bwordLength (intToPair y).2) := by
    calc
      (bwordLength (intToPair x).1 + bwordLength (intToPair z).2) +
          (bwordLength (intToPair y).1 + bwordLength (intToPair y).2)
          =
        (bwordLength (intToPair x).1 + bwordLength (intToPair y).2) +
          (bwordLength (intToPair y).1 + bwordLength (intToPair z).2) := by
            exact (nat_add_four_last_swap
              (bwordLength (intToPair x).1)
              (bwordLength (intToPair y).2)
              (bwordLength (intToPair y).1)
              (bwordLength (intToPair z).2)).symm
      _ ≤
        (bwordLength (intToPair y).1 + bwordLength (intToPair x).2) +
          (bwordLength (intToPair z).1 + bwordLength (intToPair y).2) :=
            combined
      _ =
        (bwordLength (intToPair z).1 + bwordLength (intToPair x).2) +
          (bwordLength (intToPair y).1 + bwordLength (intToPair y).2) := by
            calc
              (bwordLength (intToPair y).1 + bwordLength (intToPair x).2) +
                  (bwordLength (intToPair z).1 + bwordLength (intToPair y).2)
                  =
                (bwordLength (intToPair y).1 + bwordLength (intToPair y).2) +
                  (bwordLength (intToPair z).1 + bwordLength (intToPair x).2) := by
                    exact nat_add_four_last_swap
                      (bwordLength (intToPair y).1)
                      (bwordLength (intToPair x).2)
                      (bwordLength (intToPair z).1)
                      (bwordLength (intToPair y).2)
              _ =
                (bwordLength (intToPair z).1 + bwordLength (intToPair x).2) +
                  (bwordLength (intToPair y).1 + bwordLength (intToPair y).2) := by
                    exact Nat.add_comm
                      (bwordLength (intToPair y).1 + bwordLength (intToPair y).2)
                      (bwordLength (intToPair z).1 + bwordLength (intToPair x).2)
  exact nat_le_cancel_add_right rearranged

theorem intLe_respects {x x' y y' : RatInt} :
    IntEq x x' -> IntEq y y' -> intLe x y -> intLe x' y' := by
  intro xx' yy' xy
  unfold intLe at xy ⊢
  have hx := intToPair_carrier x
  have hx' := intToPair_carrier x'
  have hy := intToPair_carrier y
  have hy' := intToPair_carrier y'
  have xxLen := IntPairClassifier_length_eq xx'
  have yyLen := IntPairClassifier_length_eq yy'
  have xyLen := (pairLe_iff_length_order hx hy).mp xy
  apply pairLe_of_length_order hx' hy'
  exact nat_le_pair_transport xxLen yyLen xyLen

private theorem pairLe_respects_classifier {x x' y y' : BHist × BHist} :
    IntPairClassifier x x' -> IntPairClassifier y y' ->
      pairLe x y -> pairLe x' y' := by
  intro xx' yy' xy
  have xyLen := (pairLe_iff_length_order xx'.left yy'.left).mp xy
  apply pairLe_of_length_order xx'.right.left yy'.right.left
  exact nat_le_pair_transport
    (IntPairClassifier_length_eq xx') (IntPairClassifier_length_eq yy') xyLen

private theorem nat_le_mul_cancel_left_positive {c a b : Nat} :
    c * a ≤ c * b -> 0 < c -> a ≤ b := by
  intro h hc
  exact Nat.le_of_mul_le_mul_left h hc

private theorem nat_mul_right_distrib_clean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := Nat.mul_comm (a + b) c
    _ = c * a + c * b := Nat.left_distrib c a b
    _ = a * c + c * b := congrArg (fun t => t + c * b) (Nat.mul_comm c a)
    _ = a * c + b * c := congrArg (fun t => a * c + t) (Nat.mul_comm c b)

private theorem nat_pair_mul_right_nat_le
    {p n q m r : Nat} :
    p + m ≤ q + n ->
      p * r + m * r ≤ q * r + n * r := by
  intro h
  have scaled : (p + m) * r ≤ (q + n) * r :=
    Nat.mul_le_mul_right r h
  calc
    p * r + m * r = (p + m) * r :=
      (nat_mul_right_distrib_clean p m r).symm
    _ ≤ (q + n) * r := scaled
    _ = q * r + n * r :=
      nat_mul_right_distrib_clean q n r

private theorem nat_pair_mul_right_le_cancel
    {p n q m r : Nat} :
    ((p * r) + (m * r)) ≤ ((q * r) + (n * r)) ->
      0 < r -> p + m ≤ q + n := by
  intro h hr
  apply nat_le_mul_cancel_left_positive (c := r)
  · calc
      r * (p + m) = p * r + m * r := by
          rw [Nat.left_distrib]
          rw [Nat.mul_comm r p]
          rw [Nat.mul_comm r m]
      _ ≤ q * r + n * r := h
      _ = r * (q + n) := by
          rw [Nat.left_distrib]
          rw [Nat.mul_comm r q]
          rw [Nat.mul_comm r n]
  · exact hr

private theorem nat_sub_pair_le_left_of_nonneg {xp xn yp yn : Nat} :
    yn ≤ yp -> (xp + yn) + xn ≤ xp + (xn + yp) := by
  intro h
  apply nat_le_cancel_add_right (c := xp)
  calc
    ((xp + yn) + xn) + xp =
        yn + ((xp + xn) + xp) := by
          calc
            ((xp + yn) + xn) + xp =
                (xp + yn) + (xn + xp) := by
                  rw [Nat.add_assoc]
            _ =
                (xp + xn) + (yn + xp) :=
                  nat_add_four_swap xp yn xn xp
            _ = (yn + xp) + (xp + xn) := by
                  rw [Nat.add_comm]
            _ = yn + (xp + (xp + xn)) := by
                  rw [Nat.add_assoc]
            _ = yn + ((xp + xn) + xp) := by
                  rw [Nat.add_comm (xp + xn) xp]
    _ ≤ yp + ((xp + xn) + xp) :=
        Nat.add_le_add_right h _
    _ = (xp + (xn + yp)) + xp := by
        calc
          yp + ((xp + xn) + xp) =
              (yp + (xp + xn)) + xp := (Nat.add_assoc yp (xp + xn) xp).symm
          _ = ((xp + xn) + yp) + xp := by
              rw [Nat.add_comm yp (xp + xn)]
          _ = (xp + (xn + yp)) + xp := by
              rw [Nat.add_assoc xp xn yp]

theorem intLe_mul_nonneg_right_of_nat {a b : RatInt}
    (d : BHist) (hd : UnaryHistory d) :
    intLe a b ->
      intLe (IntMul a (intOfNat d hd)) (IntMul b (intOfNat d hd)) := by
  intro hle
  unfold intLe at hle ⊢
  have ha := intToPair_carrier a
  have hb := intToPair_carrier b
  have hdPair : IntPairCarrier
      (intToPair (intOfNat d hd)).1 (intToPair (intOfNat d hd)).2 :=
    intToPair_carrier (intOfNat d hd)
  have hLen := (pairLe_iff_length_order ha hb).mp hle
  have leftMul := intMul_pair_classifier a (intOfNat d hd)
  have rightMul := intMul_pair_classifier b (intOfNat d hd)
  have pairProductLe :
      pairLe
        (pairMul (intToPair a) (intToPair (intOfNat d hd)))
        (pairMul (intToPair b) (intToPair (intOfNat d hd))) := by
    apply pairLe_of_length_order (pairMul_carrier ha hdPair)
      (pairMul_carrier hb hdPair)
    rw [pairMul_pos_length (intToPair a) (intToPair (intOfNat d hd)) ha hdPair]
    rw [pairMul_neg_length (intToPair b) (intToPair (intOfNat d hd)) hb hdPair]
    rw [pairMul_pos_length (intToPair b) (intToPair (intOfNat d hd)) hb hdPair]
    rw [pairMul_neg_length (intToPair a) (intToPair (intOfNat d hd)) ha hdPair]
    unfold intOfNat intToPair
    change
      ((bwordLength (intToPair a).1 * bwordLength d +
            bwordLength (intToPair a).2 * bwordLength BHist.Empty) +
          (bwordLength (intToPair b).1 * bwordLength BHist.Empty +
            bwordLength (intToPair b).2 * bwordLength d)) ≤
        ((bwordLength (intToPair b).1 * bwordLength d +
            bwordLength (intToPair b).2 * bwordLength BHist.Empty) +
          (bwordLength (intToPair a).1 * bwordLength BHist.Empty +
            bwordLength (intToPair a).2 * bwordLength d))
    rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
    rw [Nat.mul_zero, Nat.mul_zero]
    change
      (bwordLength (intToPair a).1 * bwordLength d +
          (0 + bwordLength (intToPair b).2 * bwordLength d)) ≤
        (bwordLength (intToPair b).1 * bwordLength d + 0 +
          (0 + bwordLength (intToPair a).2 * bwordLength d))
    rw [Nat.zero_add, Nat.zero_add, Nat.add_zero]
    exact nat_pair_mul_right_nat_le (r := bwordLength d) hLen
  exact pairLe_respects_classifier
    (IntPairClassifier_equivalence_fields.right.right.right.left leftMul)
    (IntPairClassifier_equivalence_fields.right.right.right.left rightMul)
    pairProductLe

theorem intLe_mul_cancel_right_of_nat {a b : RatInt}
    (d : BHist) (hd : UnaryHistory d) (hpos : 0 < bwordLength d) :
    intLe (IntMul a (intOfNat d hd)) (IntMul b (intOfNat d hd)) ->
      intLe a b := by
  intro hle
  unfold intLe at hle ⊢
  have ha := intToPair_carrier a
  have hb := intToPair_carrier b
  have hdPair : IntPairCarrier
      (intToPair (intOfNat d hd)).1 (intToPair (intOfNat d hd)).2 :=
    intToPair_carrier (intOfNat d hd)
  have leftMul := intMul_pair_classifier a (intOfNat d hd)
  have rightMul := intMul_pair_classifier b (intOfNat d hd)
  have pairProductLe :
      pairLe
        (pairMul (intToPair a) (intToPair (intOfNat d hd)))
        (pairMul (intToPair b) (intToPair (intOfNat d hd))) := by
    exact pairLe_respects_classifier leftMul rightMul hle
  have productLen :=
    (pairLe_iff_length_order (pairMul_carrier ha hdPair)
      (pairMul_carrier hb hdPair)).mp pairProductLe
  have productLenSimple :
      bwordLength (intToPair a).1 * bwordLength d +
          bwordLength (intToPair b).2 * bwordLength d ≤
        bwordLength (intToPair b).1 * bwordLength d +
          bwordLength (intToPair a).2 * bwordLength d := by
    have h := productLen
    rw [pairMul_pos_length (intToPair a) (intToPair (intOfNat d hd)) ha hdPair] at h
    rw [pairMul_neg_length (intToPair b) (intToPair (intOfNat d hd)) hb hdPair] at h
    rw [pairMul_pos_length (intToPair b) (intToPair (intOfNat d hd)) hb hdPair] at h
    rw [pairMul_neg_length (intToPair a) (intToPair (intOfNat d hd)) ha hdPair] at h
    unfold intOfNat intToPair at h
    rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at h
    rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero, Nat.mul_zero] at h
    change
      bwordLength (intToPair a).1 * bwordLength d +
          bwordLength (intToPair b).2 * bwordLength d ≤
        bwordLength (intToPair b).1 * bwordLength d +
          bwordLength (intToPair a).2 * bwordLength d
    change
      bwordLength (intToPair a).1 * bwordLength d +
          (0 + bwordLength (intToPair b).2 * bwordLength d) ≤
        bwordLength (intToPair b).1 * bwordLength d + 0 +
          (0 + bwordLength (intToPair a).2 * bwordLength d) at h
    rw [Nat.zero_add, Nat.zero_add, Nat.add_zero] at h
    exact h
  apply pairLe_of_length_order ha hb
  apply nat_pair_mul_right_le_cancel (r := bwordLength d)
  · exact productLenSimple
  · exact hpos

private theorem ratDenInt_length_pos (x : RatNum) :
    0 < bwordLength x.den := by
  exact intApart0_length_pos (x := ratDenInt x) (ratDenInt_nonzero x)

theorem intLe_mul_ratDen_right {a b : RatInt} (x : RatNum) :
    intLe a b ->
      intLe (IntMul a (ratDenInt x)) (IntMul b (ratDenInt x)) := by
  unfold ratDenInt
  exact intLe_mul_nonneg_right_of_nat x.den (ratDenCarrier x)

theorem intLe_mul_ratDen_cancel_right {a b : RatInt} (x : RatNum) :
    intLe (IntMul a (ratDenInt x)) (IntMul b (ratDenInt x)) ->
      intLe a b := by
  unfold ratDenInt
  exact intLe_mul_cancel_right_of_nat x.den (ratDenCarrier x)
    (ratDenInt_length_pos x)

theorem intSub_nonneg_of_le {x y : RatInt} :
    intLe y x -> intLe intZero (IntAdd x (IntNeg y)) := by
  intro hle
  unfold intLe at hle ⊢
  have hx := intToPair_carrier x
  have hy := intToPair_carrier y
  have hLen := (pairLe_iff_length_order hy hx).mp hle
  let diffPair := pairAdd (intToPair x) (pairNeg (intToPair y))
  have diffPairLe :
      pairLe (BHist.Empty, BHist.Empty) diffPair := by
    apply pairLe_of_length_order ⟨unary_empty, unary_empty⟩
      (BEDC.Derived.IntUp.pairAdd_carrier hx
        (BEDC.Derived.IntUp.pairNeg_carrier hy))
    unfold BEDC.Derived.IntUp.pairAdd BEDC.Derived.IntUp.pairNeg
    rw [BEDC.FKernel.ExternalBinary.bwordLength_append,
      BEDC.FKernel.ExternalBinary.bwordLength_append]
    change
      bwordLength BHist.Empty + (bwordLength (intToPair x).2 +
          bwordLength (intToPair y).1) ≤
        (bwordLength (intToPair x).1 + bwordLength (intToPair y).2) +
          bwordLength BHist.Empty
    rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
    rw [Nat.zero_add, Nat.add_zero]
    exact Nat.add_comm _ _ ▸ hLen
  have zeroSame :
      IntPairClassifier (intToPair intZero) (BHist.Empty, BHist.Empty) :=
    IntPairClassifier_equivalence_fields.right.right.left
      (intToPair_carrier intZero)
  have diffSame :
      IntPairClassifier (intToPair (IntAdd x (IntNeg y))) diffPair := by
    unfold diffPair IntAdd IntNeg intNeg
    exact IntPairClassifier_equivalence_fields.right.right.right.right.left
      (intAdd_pair_classifier x (pairToInt (pairNeg (intToPair y))))
      (pairAdd_classifier_congr
        (IntPairClassifier_equivalence_fields.right.right.left hx)
        (intToPair_pairToInt_classifier (pairNeg (intToPair y))
          (BEDC.Derived.IntUp.pairNeg_carrier hy)))
  exact pairLe_respects_classifier
    (IntPairClassifier_equivalence_fields.right.right.right.left zeroSame)
    (IntPairClassifier_equivalence_fields.right.right.right.left diffSame)
    diffPairLe

theorem intSub_le_left_of_nonneg {x y : RatInt} :
    intLe intZero y -> intLe (IntAdd x (IntNeg y)) x := by
  intro hnonneg
  unfold intLe at hnonneg ⊢
  have hx := intToPair_carrier x
  have hy := intToPair_carrier y
  have yLen := (pairLe_iff_length_order (intToPair_carrier intZero) hy).mp hnonneg
  have yNonneg :
      bwordLength (intToPair y).2 ≤ bwordLength (intToPair y).1 := by
    unfold intZero intOfNat intToPair at yLen
    rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at yLen
    rw [Nat.zero_add, Nat.add_zero] at yLen
    exact yLen
  let diffPair := pairAdd (intToPair x) (pairNeg (intToPair y))
  have diffPairLe :
      pairLe diffPair (intToPair x) := by
    apply pairLe_of_length_order
      (BEDC.Derived.IntUp.pairAdd_carrier hx
        (BEDC.Derived.IntUp.pairNeg_carrier hy))
      hx
    unfold BEDC.Derived.IntUp.pairAdd BEDC.Derived.IntUp.pairNeg
    rw [BEDC.FKernel.ExternalBinary.bwordLength_append,
      BEDC.FKernel.ExternalBinary.bwordLength_append]
    change
      (bwordLength (intToPair x).1 + bwordLength (intToPair y).2) +
          bwordLength (intToPair x).2 ≤
        bwordLength (intToPair x).1 +
          (bwordLength (intToPair x).2 + bwordLength (intToPair y).1)
    exact nat_sub_pair_le_left_of_nonneg yNonneg
  have diffSame :
      IntPairClassifier (intToPair (IntAdd x (IntNeg y))) diffPair := by
    unfold diffPair IntAdd IntNeg intNeg
    exact IntPairClassifier_equivalence_fields.right.right.right.right.left
      (intAdd_pair_classifier x (pairToInt (pairNeg (intToPair y))))
      (pairAdd_classifier_congr
        (IntPairClassifier_equivalence_fields.right.right.left hx)
        (intToPair_pairToInt_classifier (pairNeg (intToPair y))
          (BEDC.Derived.IntUp.pairNeg_carrier hy)))
  exact pairLe_respects_classifier
    (IntPairClassifier_equivalence_fields.right.right.right.left diffSame)
    (IntPairClassifier_equivalence_fields.right.right.left hx)
    diffPairLe

theorem intLe_zero_of_nat (n : BHist) (hn : UnaryHistory n) :
    intLe intZero (intOfNat n hn) := by
  unfold intLe intZero intOfNat intToPair
  apply pairLe_of_length_order
  · exact ⟨unary_empty, unary_empty⟩
  · exact ⟨hn, unary_empty⟩
  change
    BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty +
        BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty ≤
      BEDC.FKernel.ExternalBinary.bwordLength n +
        BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
  rw [Nat.zero_add, Nat.add_zero]
  exact Nat.zero_le _

theorem intLt_to_intLe {x y : RatInt} :
    intLtUp x y -> intLe x y := by
  intro h
  change pairLe (intToPair x) (intToPair y)
  change intLt (intToPair x) (intToPair y) at h
  exact intLt_to_pairLe (intToPair_carrier x) (intToPair_carrier y) h

theorem ratLe_refl (x : RatNum) :
    ratLe x x := by
  unfold ratLe
  exact intLe_refl _

theorem ratLe_total (x y : RatNum) :
    ratLe x y ∨ ratLe y x := by
  unfold ratLe
  exact intLe_total _ _

theorem ratLe_trans {x y z : RatNum} :
    ratLe x y -> ratLe y z -> ratLe x z := by
  intro xy yz
  unfold ratLe at xy yz ⊢
  have xyScaled :
      intLe
        (IntMul (IntMul x.num (ratDenInt y)) (ratDenInt z))
        (IntMul (IntMul y.num (ratDenInt x)) (ratDenInt z)) :=
    intLe_mul_ratDen_right z xy
  have yzScaled :
      intLe
        (IntMul (IntMul y.num (ratDenInt z)) (ratDenInt x))
        (IntMul (IntMul z.num (ratDenInt y)) (ratDenInt x)) :=
    intLe_mul_ratDen_right x yz
  have leftToMid :
      intLe
        (IntMul (IntMul x.num (ratDenInt z)) (ratDenInt y))
        (IntMul (IntMul y.num (ratDenInt z)) (ratDenInt x)) :=
    intLe_respects
      (intMul_middle_swap x.num (ratDenInt y) (ratDenInt z))
      (intMul_middle_swap y.num (ratDenInt x) (ratDenInt z))
      xyScaled
  have midToRight :
      intLe
        (IntMul (IntMul y.num (ratDenInt z)) (ratDenInt x))
        (IntMul (IntMul z.num (ratDenInt x)) (ratDenInt y)) :=
    intLe_respects
      (IntEq_refl _)
      (intMul_middle_swap z.num (ratDenInt y) (ratDenInt x))
      yzScaled
  exact intLe_mul_ratDen_cancel_right y
    (intLe_trans leftToMid midToRight)

theorem ratLe_of_RatEq {x y : RatNum} :
    RatEq x y -> ratLe x y := by
  intro same
  unfold RatEq at same
  unfold ratLe
  exact intLe_respects (IntEq_refl _) same (intLe_refl _)

theorem ratLe_respects {x x' y y' : RatNum} :
    RatEq x x' -> RatEq y y' -> ratLe x y -> ratLe x' y' := by
  intro xx' yy' xy
  exact ratLe_trans (ratLe_of_RatEq (RatEq_symm xx'))
    (ratLe_trans xy (ratLe_of_RatEq yy'))

theorem intLe_mul_ratDen_right_nonneg {a : RatInt} (x : RatNum) :
    intLe intZero a -> intLe intZero (IntMul a (ratDenInt x)) := by
  intro h
  have scaled := intLe_mul_ratDen_right x h
  exact intLe_respects (intMul_zero_left (ratDenInt x)) (IntEq_refl _) scaled

theorem ratNonneg_num {x : RatNum} :
    ratLe ratZero x -> intLe intZero x.num := by
  intro hnonneg
  unfold ratLe ratZero intToRat at hnonneg
  change
    intLe (IntMul intZero (ratDenInt x))
      (IntMul x.num (ratDenInt ratZero)) at hnonneg
  have leftZero :
      IntEq (IntMul intZero (ratDenInt x)) intZero :=
    intMul_zero_left (ratDenInt x)
  have rightNum :
      IntEq (IntMul x.num (ratDenInt ratZero)) x.num :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (intMul_one_right x.num)
  exact intLe_respects leftZero rightNum hnonneg

theorem ratNonneg_of_num {x : RatNum} :
    intLe intZero x.num -> ratLe ratZero x := by
  intro hnum
  unfold ratLe ratZero intToRat
  change
    intLe (IntMul intZero (ratDenInt x))
      (IntMul x.num (ratDenInt ratZero))
  exact intLe_respects
    (IntEq_symm (intMul_zero_left (ratDenInt x)))
    (IntEq_symm
      (IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
        (intMul_one_right x.num)))
    hnum

theorem ratLt_to_ratLe {x y : RatNum} :
    ratLt x y -> ratLe x y := by
  intro h
  change intLe (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x))
  change intLtUp (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x)) at h
  exact intLt_to_intLe h

theorem ratLe_antisymm {x y : RatNum} :
    ratLe x y -> ratLe y x -> RatEq x y := by
  intro xy yx
  unfold ratLe at xy yx
  unfold RatEq
  exact intLe_antisymm xy yx

theorem ratAbs_eq_magnitude (x : RatNum) :
    RatEq (ratAbs x) (ratMagnitude x) := by
  exact RatEq_refl _

theorem ratDist_eq_abs_sub (x y : RatNum) :
    RatEq (ratDist x y) (ratAbs (ratSub x y)) := by
  exact RatEq_refl _

theorem ratLe_decidable (x y : RatNum) :
    ratLe x y ∨ (ratLe x y -> False) := by
  unfold ratLe intLe
  let left := intToPair (IntMul x.num (ratDenInt y))
  let right := intToPair (IntMul y.num (ratDenInt x))
  have leftCarrier : IntPairCarrier left.1 left.2 := by
    unfold left
    exact intToPair_carrier _
  have rightCarrier : IntPairCarrier right.1 right.2 := by
    unfold right
    exact intToPair_carrier _
  by_cases h :
      bwordLength left.1 + bwordLength right.2 ≤
        bwordLength right.1 + bwordLength left.2
  · exact Or.inl (pairLe_of_length_order leftCarrier rightCarrier h)
  · exact Or.inr (fun leProof =>
      h ((pairLe_iff_length_order leftCarrier rightCarrier).mp leProof))

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k ->
      BEDC.FKernel.ExternalBinary.bwordLength h =
        BEDC.FKernel.ExternalBinary.bwordLength k ->
        hsame h k := by
  intro hUnary kUnary lengthEq
  exact
    (BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
      hUnary kUnary).mpr lengthEq

theorem intMagnitude_eq_self_of_nonneg {x : RatInt} :
    intLe intZero x ->
      IntEq (intOfNat x.magnitude x.carrier.right) x := by
  intro hnonneg
  cases x with
  | mk sign magnitude carrier =>
      cases sign
      · exact IntPairClassifier_equivalence_fields.right.right.left
          (intToPair_carrier
            (intOfNat magnitude carrier.right))
      · have lenLe :
            bwordLength magnitude ≤ bwordLength BHist.Empty := by
          unfold intLe intZero intOfNat intToPair at hnonneg
          have len :=
            (pairLe_iff_length_order
              ⟨unary_empty, unary_empty⟩
              ⟨unary_empty, carrier.right⟩).mp hnonneg
          rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at len
          rw [Nat.zero_add, Nat.add_zero] at len
          exact len
        have magLenZero : bwordLength magnitude = 0 := by
          rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at lenLe
          exact Nat.eq_zero_of_le_zero lenLe
        unfold IntEq intOfNat intToPair
        apply IntPairClassifier_of_length_eq
        · exact ⟨carrier.right, unary_empty⟩
        · exact ⟨unary_empty, carrier.right⟩
        rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
        rw [magLenZero]

theorem ratMagnitude_eq_self_of_nonneg {x : RatNum} :
    ratLe ratZero x -> RatEq (ratMagnitude x) x := by
  intro hnonneg
  have numNonneg : intLe intZero x.num := by
    unfold ratLe ratZero intToRat at hnonneg
    change
      intLe (IntMul intZero (ratDenInt x))
        (IntMul x.num (ratDenInt ratZero)) at hnonneg
    have leftZero :
        IntEq (IntMul intZero (ratDenInt x)) intZero :=
      intMul_zero_left (ratDenInt x)
    have rightNum :
        IntEq (IntMul x.num (ratDenInt ratZero)) x.num :=
      IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
        (intMul_one_right x.num)
    exact intLe_respects leftZero rightNum hnonneg
  apply ratEq_of_num_den_intEq
  · unfold ratMagnitude
    exact intMagnitude_eq_self_of_nonneg numNonneg
  · unfold ratMagnitude ratDenInt
    exact IntEq_refl (intOfNat x.den (ratDenCarrier x))

private theorem IntEq_zero_magnitude_empty {x : RatInt} :
    IntEq x intZero -> hsame x.magnitude BHist.Empty := by
  intro same
  cases x with
  | mk sign magnitude carrier =>
      cases sign
      · have lenEq := IntPairClassifier_length_eq same
        change
          BEDC.FKernel.ExternalBinary.bwordLength magnitude +
              BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty =
            BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty +
              BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty at lenEq
        rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at lenEq
        rw [Nat.add_zero, Nat.zero_add] at lenEq
        exact unary_hsame_of_length carrier.right unary_empty lenEq
      · have lenEq := IntPairClassifier_length_eq same
        change
          BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty +
              BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty =
            BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty +
              BEDC.FKernel.ExternalBinary.bwordLength magnitude at lenEq
        rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at lenEq
        simp only [Nat.zero_add] at lenEq
        exact unary_hsame_of_length carrier.right unary_empty lenEq.symm

private theorem IntEq_zero_of_magnitude_empty {x : RatInt} :
    hsame x.magnitude BHist.Empty -> IntEq x intZero := by
  intro magEmpty
  cases x with
  | mk sign magnitude carrier =>
      cases sign
      · unfold IntEq intZero intOfNat intToPair
        apply IntPairClassifier_of_length_eq
        · exact ⟨carrier.right, unary_empty⟩
        · exact ⟨unary_empty, unary_empty⟩
        change
          BEDC.FKernel.ExternalBinary.bwordLength magnitude +
              BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty =
            BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty +
              BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty
        rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
        rw [Nat.add_zero, Nat.zero_add]
        exact congrArg BEDC.FKernel.ExternalBinary.bwordLength magEmpty
      · unfold IntEq intZero intOfNat intToPair
        apply IntPairClassifier_of_length_eq
        · exact ⟨unary_empty, carrier.right⟩
        · exact ⟨unary_empty, unary_empty⟩
        change
          BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty +
              BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty =
            BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty +
              BEDC.FKernel.ExternalBinary.bwordLength magnitude
        rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
        rw [Nat.zero_add, Nat.zero_add]
        exact (congrArg BEDC.FKernel.ExternalBinary.bwordLength magEmpty).symm

theorem RatEq_zero_num {x : RatNum} :
    RatEq x ratZero -> IntEq x.num intZero := by
  intro same
  unfold RatEq at same
  change
    IntEq (IntMul x.num (ratDenInt ratZero))
      (IntMul ratZero.num (ratDenInt x)) at same
  have leftToNum :
      IntEq (IntMul x.num (ratDenInt ratZero)) x.num :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (intMul_one_right x.num)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans (IntEq_symm leftToNum)
    (IntEq_trans same rightToZero)

private theorem ratNum_zero_to_RatEq_zero {x : RatNum} :
    IntEq x.num intZero -> RatEq x ratZero := by
  intro numZero
  unfold RatEq
  change
    IntEq (IntMul x.num (ratDenInt ratZero))
      (IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

theorem ratMagnitude_eq_zero_of_RatEq_zero {x : RatNum} :
    RatEq x ratZero -> RatEq (ratMagnitude x) ratZero := by
  intro same
  have numZero : IntEq x.num intZero := RatEq_zero_num same
  have magnitudeEmpty : hsame x.num.magnitude BHist.Empty :=
    IntEq_zero_magnitude_empty numZero
  have magnitudeNumZero :
      IntEq (ratMagnitude x).num intZero := by
    unfold ratMagnitude intZero
    exact intOfNat_hsame_congr x.num.carrier.right unary_empty magnitudeEmpty
  exact ratNum_zero_to_RatEq_zero magnitudeNumZero

theorem ratMagnitude_zero_iff (x : RatNum) :
    RatEq (ratMagnitude x) ratZero ↔ RatEq x ratZero := by
  constructor
  · intro magZero
    have magNumZero : IntEq (ratMagnitude x).num intZero :=
      RatEq_zero_num magZero
    have magnitudeEmpty : hsame x.num.magnitude BHist.Empty := by
      change IntEq (intOfNat x.num.magnitude x.num.carrier.right) intZero at magNumZero
      exact
        IntEq_zero_magnitude_empty
          (x := intOfNat x.num.magnitude x.num.carrier.right) magNumZero
    exact ratNum_zero_to_RatEq_zero
      (IntEq_zero_of_magnitude_empty magnitudeEmpty)
  · intro zero
    exact ratMagnitude_eq_zero_of_RatEq_zero zero

private theorem IntNeg_magnitude_hsame (x : RatInt) :
    hsame (IntNeg x).magnitude x.magnitude := by
  cases x with
  | mk sign magnitude carrier =>
      cases sign
      · have same :
          IntEq
            (IntNeg
              { sign := BMark.b0, magnitude := magnitude, carrier := carrier })
            (intOfNatWithSign BMark.b1 magnitude carrier.right) := by
          unfold IntEq IntNeg intNeg intOfNatWithSign intToPair BEDC.Derived.IntUp.pairNeg
          exact intToPair_pairToInt_classifier
            (BHist.Empty, magnitude) ⟨unary_empty, carrier.right⟩
        have magSame :
            hsame
              (IntNeg
                { sign := BMark.b0, magnitude := magnitude, carrier := carrier }).magnitude
              (intOfNatWithSign BMark.b1 magnitude carrier.right).magnitude :=
          IntEq_magnitude_hsame
            (x := IntNeg
              { sign := BMark.b0, magnitude := magnitude, carrier := carrier })
            (y := intOfNatWithSign BMark.b1 magnitude carrier.right) same
        exact magSame
      · have same :
          IntEq
            (IntNeg
              { sign := BMark.b1, magnitude := magnitude, carrier := carrier })
            (intOfNatWithSign BMark.b0 magnitude carrier.right) := by
          unfold IntEq IntNeg intNeg intOfNatWithSign intToPair BEDC.Derived.IntUp.pairNeg
          exact intToPair_pairToInt_classifier
            (magnitude, BHist.Empty) ⟨carrier.right, unary_empty⟩
        have magSame :
            hsame
              (IntNeg
                { sign := BMark.b1, magnitude := magnitude, carrier := carrier }).magnitude
              (intOfNatWithSign BMark.b0 magnitude carrier.right).magnitude :=
          IntEq_magnitude_hsame
            (x := IntNeg
              { sign := BMark.b1, magnitude := magnitude, carrier := carrier })
            (y := intOfNatWithSign BMark.b0 magnitude carrier.right) same
        exact magSame

private theorem intAdd_neg_eq_zero_to_eq {a b : RatInt} :
    IntEq (IntAdd a (IntNeg b)) intZero -> IntEq a b := by
  intro h
  have addB :
      IntEq (IntAdd (IntAdd a (IntNeg b)) b)
        (IntAdd intZero b) :=
    IntAdd_respects h (IntEq_refl b)
  have leftNorm :
      IntEq (IntAdd (IntAdd a (IntNeg b)) b) a := by
    exact IntEq_trans (IntAdd_assoc a (IntNeg b) b)
      (IntEq_trans
        (intAdd_left_congr (c := a) (IntAdd_neg_left b))
        (IntAdd_zero a))
  have rightNorm : IntEq (IntAdd intZero b) b :=
    IntAdd_zero_left b
  exact IntEq_trans (IntEq_symm leftNorm)
    (IntEq_trans addB rightNorm)

private theorem intSub_swap_neg (a b : RatInt) :
    IntEq (IntAdd a (IntNeg b)) (IntNeg (IntAdd b (IntNeg a))) := by
  let R := BEDC.Algebra.Rel.IntegerUp_RelCommRing
  apply R.eq_neg_of_add_eq_zero
    (a := IntAdd b (IntNeg a)) (b := IntAdd a (IntNeg b))
  have inner :
      IntEq (IntAdd (IntNeg a) (IntAdd a (IntNeg b))) (IntNeg b) := by
    exact IntEq_trans
      (IntEq_symm (IntAdd_assoc (IntNeg a) a (IntNeg b)))
      (IntEq_trans
        (intAdd_right_congr (IntAdd_neg_left a))
        (IntAdd_zero_left (IntNeg b)))
  exact IntEq_trans
    (IntAdd_assoc b (IntNeg a) (IntAdd a (IntNeg b)))
    (IntEq_trans
      (intAdd_left_congr (c := b) inner)
      (IntAdd_neg b))

private theorem ratDenInt_neg (x : RatNum) :
    IntEq (ratDenInt (ratNeg x)) (ratDenInt x) := by
  unfold ratDenInt ratNeg
  exact IntEq_refl (intOfNat x.den (ratDenCarrier x))

theorem ratSub_nonneg_of_le {x y : RatNum} :
    ratLe y x -> ratLe ratZero (ratAdd x (ratNeg y)) := by
  intro hle
  unfold ratLe at hle
  have core :
      intLe intZero
        (IntAdd (IntMul x.num (ratDenInt y))
          (IntNeg (IntMul y.num (ratDenInt x)))) :=
    intSub_nonneg_of_le hle
  have negTerm :
      IntEq (IntMul (IntNeg y.num) (ratDenInt x))
        (IntNeg (IntMul y.num (ratDenInt x))) :=
    BEDC.Algebra.Rel.IntegerUp_neg_mul y.num (ratDenInt x)
  have numEq :
      IntEq
        (IntAdd (IntMul x.num (ratDenInt y))
          (IntMul (IntNeg y.num) (ratDenInt x)))
        (IntAdd (IntMul x.num (ratDenInt y))
          (IntNeg (IntMul y.num (ratDenInt x)))) :=
    IntAdd_respects (IntEq_refl _) negTerm
  apply ratNonneg_of_num
  unfold ratAdd ratNeg
  change
    intLe intZero
      (IntAdd (IntMul x.num (ratDenInt y))
        (IntMul (IntNeg y.num) (ratDenInt x)))
  exact intLe_respects (IntEq_refl intZero) (IntEq_symm numEq) core

private theorem ratSub_left_cross_eq {x y : RatNum} :
    IntEq
      (IntMul
        (IntAdd (IntMul x.num (ratDenInt y))
          (IntMul (IntNeg y.num) (ratDenInt x)))
        (ratDenInt x))
      (IntAdd
        (IntMul (IntMul x.num (ratDenInt y)) (ratDenInt x))
        (IntNeg (IntMul (IntMul y.num (ratDenInt x)) (ratDenInt x)))) := by
  have distrib :
      IntEq
        (IntMul
          (IntAdd (IntMul x.num (ratDenInt y))
            (IntMul (IntNeg y.num) (ratDenInt x)))
          (ratDenInt x))
        (IntAdd
          (IntMul (IntMul x.num (ratDenInt y)) (ratDenInt x))
          (IntMul (IntMul (IntNeg y.num) (ratDenInt x)) (ratDenInt x))) :=
    IntMul_add_distrib_right
      (IntMul x.num (ratDenInt y))
      (IntMul (IntNeg y.num) (ratDenInt x))
      (ratDenInt x)
  have negInner :
      IntEq (IntMul (IntNeg y.num) (ratDenInt x))
        (IntNeg (IntMul y.num (ratDenInt x))) :=
    BEDC.Algebra.Rel.IntegerUp_neg_mul y.num (ratDenInt x)
  have negProduct :
      IntEq
        (IntMul (IntMul (IntNeg y.num) (ratDenInt x)) (ratDenInt x))
        (IntNeg (IntMul (IntMul y.num (ratDenInt x)) (ratDenInt x))) :=
    IntEq_trans
      (intMul_right_congr negInner)
      (BEDC.Algebra.Rel.IntegerUp_neg_mul
        (IntMul y.num (ratDenInt x)) (ratDenInt x))
  exact IntEq_trans distrib
    (IntAdd_respects (IntEq_refl _) negProduct)

private theorem ratSub_right_cross_eq {x y : RatNum} :
    IntEq
      (IntMul x.num (ratDenInt (ratAdd x (ratNeg y))))
      (IntMul (IntMul x.num (ratDenInt y)) (ratDenInt x)) := by
  have denStructured :
      IntEq (ratDenInt (ratAdd x (ratNeg y)))
        (IntMul (ratDenInt x) (ratDenInt y)) :=
    IntEq_trans (ratDenInt_add x (ratNeg y))
      (IntMul_respects (IntEq_refl (ratDenInt x)) (ratDenInt_neg y))
  exact IntEq_trans
    (intMul_left_congr denStructured)
    (IntEq_trans
      (IntEq_symm (intMul_assoc x.num (ratDenInt x) (ratDenInt y)))
      (intMul_middle_swap x.num (ratDenInt x) (ratDenInt y)))

theorem ratSub_le_left_of_nonneg {x y : RatNum} :
    ratLe ratZero y -> ratLe (ratAdd x (ratNeg y)) x := by
  intro yNonneg
  have yNumNonneg : intLe intZero y.num :=
    ratNonneg_num yNonneg
  have yScaledOnce :
      intLe intZero (IntMul y.num (ratDenInt x)) :=
    intLe_mul_ratDen_right_nonneg x yNumNonneg
  have yScaledTwice :
      intLe intZero
        (IntMul (IntMul y.num (ratDenInt x)) (ratDenInt x)) :=
    intLe_mul_ratDen_right_nonneg x yScaledOnce
  have core :
      intLe
        (IntAdd
          (IntMul (IntMul x.num (ratDenInt y)) (ratDenInt x))
          (IntNeg (IntMul (IntMul y.num (ratDenInt x)) (ratDenInt x))))
        (IntMul (IntMul x.num (ratDenInt y)) (ratDenInt x)) :=
    intSub_le_left_of_nonneg yScaledTwice
  unfold ratLe ratAdd ratNeg
  change
    intLe
      (IntMul
        (IntAdd (IntMul x.num (ratDenInt y))
          (IntMul (IntNeg y.num) (ratDenInt x)))
        (ratDenInt x))
      (IntMul x.num (ratDenInt (ratAdd x (ratNeg y))))
  exact intLe_respects
    (IntEq_symm (ratSub_left_cross_eq (x := x) (y := y)))
    (IntEq_symm (ratSub_right_cross_eq (x := x) (y := y)))
    core

theorem ratSub_self (x : RatNum) :
    RatEq (ratSub x x) ratZero := by
  have numZero : IntEq (ratSub x x).num intZero := by
    unfold ratSub ratAdd ratNeg
    change
      IntEq
        (IntAdd (IntMul x.num (ratDenInt x))
          (IntMul (IntNeg x.num) (ratDenInt x))) intZero
    have negMul :
        IntEq (IntMul (IntNeg x.num) (ratDenInt x))
          (IntNeg (IntMul x.num (ratDenInt x))) :=
      BEDC.Algebra.Rel.IntegerUp_neg_mul x.num (ratDenInt x)
    exact IntEq_trans
      (intAdd_left_congr (c := IntMul x.num (ratDenInt x)) negMul)
      (IntAdd_neg (IntMul x.num (ratDenInt x)))
  exact ratNum_zero_to_RatEq_zero numZero

theorem ratDist_self (x : RatNum) :
    RatEq (ratDist x x) ratZero := by
  unfold ratDist ratAbs
  exact ratMagnitude_eq_zero_of_RatEq_zero (ratSub_self x)

theorem ratSub_swap_neg (x y : RatNum) :
    RatEq (ratSub x y) (ratNeg (ratSub y x)) := by
  unfold RatEq ratSub ratAdd ratNeg
  change IntEq
    (IntMul
      (IntAdd (IntMul x.num (ratDenInt y))
        (IntMul (IntNeg y.num) (ratDenInt x)))
      (ratDenInt (ratNeg (ratAdd y (ratNeg x)))))
    (IntMul
      (IntNeg
        (IntAdd (IntMul y.num (ratDenInt x))
          (IntMul (IntNeg x.num) (ratDenInt y))))
      (ratDenInt (ratAdd x (ratNeg y))))
  have leftDen :
      IntEq (ratDenInt (ratNeg (ratAdd y (ratNeg x))))
        (IntMul (ratDenInt y) (ratDenInt x)) := by
    exact IntEq_trans (ratDenInt_neg (ratAdd y (ratNeg x)))
      (IntEq_trans (ratDenInt_add y (ratNeg x))
        (IntMul_respects (IntEq_refl (ratDenInt y)) (ratDenInt_neg x)))
  have rightDen :
      IntEq (ratDenInt (ratAdd x (ratNeg y)))
        (IntMul (ratDenInt x) (ratDenInt y)) := by
    exact IntEq_trans (ratDenInt_add x (ratNeg y))
      (IntMul_respects (IntEq_refl (ratDenInt x)) (ratDenInt_neg y))
  have numSwap :
      IntEq
        (IntAdd (IntMul x.num (ratDenInt y))
          (IntMul (IntNeg y.num) (ratDenInt x)))
        (IntNeg
          (IntAdd (IntMul y.num (ratDenInt x))
            (IntMul (IntNeg x.num) (ratDenInt y)))) := by
    have leftNeg :
        IntEq (IntMul (IntNeg y.num) (ratDenInt x))
          (IntNeg (IntMul y.num (ratDenInt x))) :=
      BEDC.Algebra.Rel.IntegerUp_neg_mul y.num (ratDenInt x)
    have rightNeg :
        IntEq (IntMul (IntNeg x.num) (ratDenInt y))
          (IntNeg (IntMul x.num (ratDenInt y))) :=
      BEDC.Algebra.Rel.IntegerUp_neg_mul x.num (ratDenInt y)
    exact IntEq_trans
      (intAdd_left_congr (c := IntMul x.num (ratDenInt y)) leftNeg)
      (IntEq_trans
        (intSub_swap_neg
          (IntMul x.num (ratDenInt y))
          (IntMul y.num (ratDenInt x)))
        (IntNeg_respects
          (IntAdd_respects (IntEq_refl (IntMul y.num (ratDenInt x)))
            (IntEq_symm rightNeg))))
  exact IntEq_trans
    (intMul_left_congr leftDen)
    (IntEq_trans
      (IntEq_trans
        (intMul_right_congr numSwap)
        (intMul_left_congr (c :=
          IntNeg
            (IntAdd (IntMul y.num (ratDenInt x))
              (IntMul (IntNeg x.num) (ratDenInt y))))
          (IntMul_comm (ratDenInt y) (ratDenInt x))))
      (IntEq_symm (intMul_left_congr rightDen)))

theorem ratSub_zero_iff (x y : RatNum) :
    RatEq (ratSub x y) ratZero ↔ RatEq x y := by
  constructor
  · intro subZero
    have numZero : IntEq (ratSub x y).num intZero :=
      RatEq_zero_num subZero
    unfold ratSub ratAdd ratNeg at numZero
    change
      IntEq
        (IntAdd (IntMul x.num (ratDenInt y))
          (IntMul (IntNeg y.num) (ratDenInt x))) intZero at numZero
    have negTerm :
        IntEq (IntMul (IntNeg y.num) (ratDenInt x))
          (IntNeg (IntMul y.num (ratDenInt x))) :=
      BEDC.Algebra.Rel.IntegerUp_neg_mul y.num (ratDenInt x)
    have normalized :
      IntEq
        (IntAdd (IntMul x.num (ratDenInt y))
          (IntNeg (IntMul y.num (ratDenInt x)))) intZero :=
      IntEq_trans
        (IntEq_symm
          (IntAdd_respects (IntEq_refl (IntMul x.num (ratDenInt y))) negTerm))
        numZero
    unfold RatEq
    change IntEq (IntMul x.num (ratDenInt y))
      (IntMul y.num (ratDenInt x))
    exact intAdd_neg_eq_zero_to_eq normalized
  · intro same
    have numZero : IntEq (ratSub x y).num intZero := by
      unfold ratSub ratAdd ratNeg
      change
        IntEq
          (IntAdd (IntMul x.num (ratDenInt y))
            (IntMul (IntNeg y.num) (ratDenInt x))) intZero
      have negTerm :
          IntEq (IntMul (IntNeg y.num) (ratDenInt x))
            (IntNeg (IntMul y.num (ratDenInt x))) :=
        BEDC.Algebra.Rel.IntegerUp_neg_mul y.num (ratDenInt x)
      have sameInt :
          IntEq (IntMul x.num (ratDenInt y))
            (IntMul y.num (ratDenInt x)) := by
        unfold RatEq at same
        change IntEq (IntMul x.num (ratDenInt y))
          (IntMul y.num (ratDenInt x)) at same
        exact same
      exact IntEq_trans
        (intAdd_left_congr (c := IntMul x.num (ratDenInt y)) negTerm)
        (IntEq_trans
          (IntAdd_respects (IntEq_refl _)
            (IntNeg_respects (IntEq_symm sameInt)))
          (IntAdd_neg (IntMul x.num (ratDenInt y))))
    exact ratNum_zero_to_RatEq_zero numZero

theorem ratDist_zero_iff (x y : RatNum) :
    RatEq (ratDist x y) ratZero ↔ RatEq x y := by
  unfold ratDist ratAbs
  exact Iff.trans (ratMagnitude_zero_iff (ratSub x y)) (ratSub_zero_iff x y)

theorem ratMagnitude_neg (x : RatNum) :
    RatEq (ratMagnitude (ratNeg x)) (ratMagnitude x) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMagnitude
    exact intOfNat_hsame_congr
      (ratNeg x).num.carrier.right x.num.carrier.right
      (IntNeg_magnitude_hsame x.num)
  · unfold ratMagnitude ratNeg
    exact IntEq_refl (ratDenInt x)

theorem ratDist_symm (x y : RatNum) :
    RatEq (ratDist x y) (ratDist y x) := by
  unfold ratDist ratAbs
  apply ratEq_of_num_den_intEq
  · unfold ratSub ratAdd ratNeg ratMagnitude
    have leftNeg :
        IntEq (IntMul (IntNeg y.num) (ratDenInt x))
          (IntNeg (IntMul y.num (ratDenInt x))) :=
      BEDC.Algebra.Rel.IntegerUp_neg_mul y.num (ratDenInt x)
    have rightNeg :
        IntEq (IntMul (IntNeg x.num) (ratDenInt y))
          (IntNeg (IntMul x.num (ratDenInt y))) :=
      BEDC.Algebra.Rel.IntegerUp_neg_mul x.num (ratDenInt y)
    have numeratorSame :
        IntEq
          (IntAdd (IntMul x.num (ratDenInt y))
            (IntMul (IntNeg y.num) (ratDenInt x)))
          (IntNeg
            (IntAdd (IntMul y.num (ratDenInt x))
              (IntMul (IntNeg x.num) (ratDenInt y)))) := by
      exact IntEq_trans
        (intAdd_left_congr (c := IntMul x.num (ratDenInt y)) leftNeg)
        (IntEq_trans
          (intSub_swap_neg
            (IntMul x.num (ratDenInt y))
            (IntMul y.num (ratDenInt x)))
          (IntNeg_respects
            (IntAdd_respects (IntEq_refl (IntMul y.num (ratDenInt x)))
              (IntEq_symm rightNeg))))
    exact intOfNat_hsame_congr
      (IntAdd (IntMul x.num (ratDenInt y))
        (IntMul (IntNeg y.num) (ratDenInt x))).carrier.right
      (IntAdd (IntMul y.num (ratDenInt x))
        (IntMul (IntNeg x.num) (ratDenInt y))).carrier.right
      (hsame_trans
        (IntEq_magnitude_hsame numeratorSame)
        (IntNeg_magnitude_hsame
          (IntAdd (IntMul y.num (ratDenInt x))
            (IntMul (IntNeg x.num) (ratDenInt y)))))
  · unfold ratSub ratAdd ratNeg ratMagnitude
    exact IntEq_trans
      (ratDenInt_add x (ratNeg y))
      (IntEq_trans
        (IntMul_respects (IntEq_refl (ratDenInt x)) (ratDenInt_neg y))
        (IntEq_trans (IntMul_comm (ratDenInt x) (ratDenInt y))
          (IntEq_symm
            (IntEq_trans (ratDenInt_add y (ratNeg x))
              (IntMul_respects (IntEq_refl (ratDenInt y)) (ratDenInt_neg x))))))

theorem ratMagnitude_nonneg (x : RatNum) :
    ratLe ratZero (ratMagnitude x) := by
  unfold ratLe ratMagnitude ratDenInt ratZero intToRat
  change intLe
    (IntMul intZero
      (intOfNat x.den (ratDenCarrier (ratMagnitude x))))
    (IntMul (intOfNat x.num.magnitude x.num.carrier.right)
      (intOfNat BEDC.Derived.PadicUp.NatOne (unary_e1_closed unary_empty)))
  exact intLe_respects
    (IntEq_symm
      (intMul_zero_left
        (intOfNat x.den (ratDenCarrier (ratMagnitude x)))))
    (IntEq_symm
      (intMul_one_right
        (intOfNat x.num.magnitude x.num.carrier.right)))
    (intLe_zero_of_nat x.num.magnitude x.num.carrier.right)

theorem ratDist_nonneg (x y : RatNum) :
    ratLe ratZero (ratDist x y) := by
  unfold ratDist ratAbs
  exact ratMagnitude_nonneg (ratSub x y)

theorem ratAbs_le_of_nonneg_le {x y : RatNum} :
    ratLe ratZero x -> ratLe x y -> ratLe (ratAbs x) y := by
  intro xNonneg xy
  unfold ratAbs
  exact ratLe_respects (RatEq_symm (ratMagnitude_eq_self_of_nonneg xNonneg))
    (RatEq_refl y) xy

theorem ratNeg_respects {x y : RatNum} :
    RatEq x y -> RatEq (ratNeg x) (ratNeg y) := by
  intro h
  unfold RatEq at h
  unfold RatEq ratNeg
  have left :
      IntEq
        (IntMul (IntNeg x.num) (ratDenInt y))
        (IntNeg (IntMul x.num (ratDenInt y))) :=
    BEDC.Algebra.Rel.IntegerUp_neg_mul x.num (ratDenInt y)
  have middle :
      IntEq
        (IntNeg (IntMul x.num (ratDenInt y)))
        (IntNeg (IntMul y.num (ratDenInt x))) :=
    IntNeg_respects h
  have right :
      IntEq
        (IntNeg (IntMul y.num (ratDenInt x)))
        (IntMul (IntNeg y.num) (ratDenInt x)) :=
    IntEq_symm (BEDC.Algebra.Rel.IntegerUp_neg_mul y.num (ratDenInt x))
  exact IntEq_trans left (IntEq_trans middle right)

private theorem intMul_cross_four {a b a' b' c d : RatInt} :
    IntEq (IntMul a b) (IntMul a' b') ->
      IntEq (IntMul (IntMul a c) (IntMul b d))
        (IntMul (IntMul a' d) (IntMul b' c)) := by
  intro h
  exact IntEq_trans (intMul_two_by_two_swap a c b d)
    (IntEq_trans
      (intMul_right_congr h)
      (IntEq_trans
        (intMul_left_congr (c := IntMul a' b') (IntMul_comm c d))
        (IntEq_symm (intMul_two_by_two_swap a' d b' c))))

private theorem intMul_cross_four_right {a b a' b' c d : RatInt} :
    IntEq (IntMul a b) (IntMul a' b') ->
      IntEq (IntMul (IntMul a c) (IntMul d b))
        (IntMul (IntMul a' d) (IntMul c b')) := by
  intro h
  exact IntEq_trans
    (intMul_left_congr (c := IntMul a c) (IntMul_comm d b))
    (IntEq_trans
      (intMul_cross_four (a := a) (b := b) (a' := a') (b' := b') (c := c) (d := d) h)
      (intMul_left_congr (c := IntMul a' d) (IntMul_comm b' c)))

theorem ratAdd_respects {x x' y y' : RatNum} :
    RatEq x x' -> RatEq y y' ->
      RatEq (ratAdd x y) (ratAdd x' y') := by
  intro xx' yy'
  unfold RatEq at xx' yy' ⊢
  change
    IntEq
      (IntMul
        (IntAdd (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x)))
        (ratDenInt (ratAdd x' y')))
      (IntMul
        (IntAdd (IntMul x'.num (ratDenInt y')) (IntMul y'.num (ratDenInt x')))
        (ratDenInt (ratAdd x y)))
  have leftDen :
      IntEq (ratDenInt (ratAdd x' y'))
        (IntMul (ratDenInt x') (ratDenInt y')) :=
    ratDenInt_add x' y'
  have rightDen :
      IntEq (ratDenInt (ratAdd x y))
        (IntMul (ratDenInt x) (ratDenInt y)) :=
    ratDenInt_add x y
  have leftToStructured :
      IntEq
        (IntMul
          (IntAdd (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x)))
          (ratDenInt (ratAdd x' y')))
        (IntMul
          (IntAdd (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x)))
          (IntMul (ratDenInt x') (ratDenInt y'))) :=
    intMul_left_congr leftDen
  have rightToStructured :
      IntEq
        (IntMul
          (IntAdd (IntMul x'.num (ratDenInt y')) (IntMul y'.num (ratDenInt x')))
          (ratDenInt (ratAdd x y)))
        (IntMul
          (IntAdd (IntMul x'.num (ratDenInt y')) (IntMul y'.num (ratDenInt x')))
          (IntMul (ratDenInt x) (ratDenInt y))) :=
    intMul_left_congr rightDen
  have firstTerm :
      IntEq
        (IntMul (IntMul x.num (ratDenInt y))
          (IntMul (ratDenInt x') (ratDenInt y')))
        (IntMul (IntMul x'.num (ratDenInt y'))
          (IntMul (ratDenInt x) (ratDenInt y))) := by
    exact intMul_cross_four
      (a := x.num) (b := ratDenInt x') (a' := x'.num) (b' := ratDenInt x)
      (c := ratDenInt y) (d := ratDenInt y') xx'
  have secondTerm :
      IntEq
        (IntMul (IntMul y.num (ratDenInt x))
          (IntMul (ratDenInt x') (ratDenInt y')))
        (IntMul (IntMul y'.num (ratDenInt x'))
          (IntMul (ratDenInt x) (ratDenInt y))) := by
    exact intMul_cross_four_right
      (a := y.num) (b := ratDenInt y') (a' := y'.num) (b' := ratDenInt y)
      (c := ratDenInt x) (d := ratDenInt x') yy'
  have structured :
      IntEq
        (IntMul
          (IntAdd (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x)))
          (IntMul (ratDenInt x') (ratDenInt y')))
        (IntMul
          (IntAdd (IntMul x'.num (ratDenInt y')) (IntMul y'.num (ratDenInt x')))
          (IntMul (ratDenInt x) (ratDenInt y))) := by
    exact IntEq_trans
      (IntMul_add_distrib_right (IntMul x.num (ratDenInt y))
        (IntMul y.num (ratDenInt x))
        (IntMul (ratDenInt x') (ratDenInt y')))
      (IntEq_trans
        (IntAdd_respects firstTerm secondTerm)
        (IntEq_symm
          (IntMul_add_distrib_right (IntMul x'.num (ratDenInt y'))
            (IntMul y'.num (ratDenInt x'))
            (IntMul (ratDenInt x) (ratDenInt y)))))
  exact IntEq_trans leftToStructured
    (IntEq_trans structured (IntEq_symm rightToStructured))

def ratHalf : RatNum :=
  { num := intOne
    den := BHist.e1 BEDC.Derived.PadicUp.NatOne
    den_pos :=
      Or.inl
        ⟨BEDC.Derived.PadicUp.NatOne, unary_e1_closed unary_empty,
          BEDC.FKernel.Hist.not_hsame_e1_empty, rfl⟩ }

def ratMidpoint (x y : RatNum) : RatNum :=
  ratMul (ratAdd x y) ratHalf

structure RatDenseBetween (x y : RatNum) where
  point : RatNum
  left : ratLt x point
  right : ratLt point y

end BEDC.Derived.RationalUp
