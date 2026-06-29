import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

namespace BEDC.Real.RatNumLogEnclosure

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.PadicUp

abbrev Rat : Type :=
  RatNumKernel.Rat

def ratThree : Rat :=
  ratNat 3

theorem ratOne_nonneg :
    ratLe ratZero ratOne := by
  apply ratNonneg_of_num
  unfold ratOne intToRat intOne intOfNat
  exact intLe_zero_of_nat NatOne (unary_e1_closed unary_empty)

theorem ratOne_apart :
    ratApart0 ratOne := by
  unfold ratApart0 ratOne intToRat intOne intOfNat
  exact Or.inr (hsame_refl NatOne)

theorem ratOne_pos :
    ratLt ratZero ratOne := by
  apply ratLe_not_le_to_ratLt
  · exact ratOne_nonneg
  · intro oneLeZero
    exact intApart0_not_zero_pair ratOne_apart
      (RatEq_zero_num (ratLe_antisymm oneLeZero ratOne_nonneg))

private theorem intLt_nat_of_lt (m n : Nat) (h : m < n) :
    intLtUp
      (intOfNat (BEDC.Derived.IntUp.natToUnary m)
        (BEDC.Derived.IntUp.natToUnary_unary m))
      (intOfNat (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary_unary n)) := by
  unfold intLtUp BEDC.Derived.IntUp.intLt intOfNat intToPair
  rw [BEDC.Derived.IntUp.natToUnary_length]
  rw [BEDC.Derived.IntUp.natToUnary_length]
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
  rw [Nat.add_zero]
  exact h

theorem ratNat_pos_of_pos {n : Nat} (h : 0 < n) :
    ratLt ratZero (ratNat n) := by
  unfold ratLt ratZero ratNat intToRat ratDenInt
  change intLtUp
    (IntMul intZero (intOfNat NatOne (unary_e1_closed unary_empty)))
    (IntMul
      (intOfNat (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary_unary n))
      (intOfNat NatOne (unary_e1_closed unary_empty)))
  have leftZero :
      IntEq
        (IntMul intZero (intOfNat NatOne (unary_e1_closed unary_empty)))
        intZero :=
    intMul_zero_left (intOfNat NatOne (unary_e1_closed unary_empty))
  have rightId :
      IntEq
        (IntMul
          (intOfNat (BEDC.Derived.IntUp.natToUnary n)
            (BEDC.Derived.IntUp.natToUnary_unary n))
          (intOfNat NatOne (unary_e1_closed unary_empty)))
        (intOfNat (BEDC.Derived.IntUp.natToUnary n)
          (BEDC.Derived.IntUp.natToUnary_unary n)) :=
    intMul_one_right
      (intOfNat (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary_unary n))
  exact intLt_respects (IntEq_symm leftZero) (IntEq_symm rightId)
    (intLt_nat_of_lt 0 n h)

theorem ratNat_lt_of_nat_lt {m n : Nat} (h : m < n) :
    ratLt (ratNat m) (ratNat n) := by
  unfold ratLt ratNat ratDenInt
  change intLtUp
    (IntMul
      (intOfNat (BEDC.Derived.IntUp.natToUnary m)
        (BEDC.Derived.IntUp.natToUnary_unary m))
      (intOfNat NatOne (unary_e1_closed unary_empty)))
    (IntMul
      (intOfNat (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary_unary n))
      (intOfNat NatOne (unary_e1_closed unary_empty)))
  have leftId :
      IntEq
        (IntMul
          (intOfNat (BEDC.Derived.IntUp.natToUnary m)
            (BEDC.Derived.IntUp.natToUnary_unary m))
          (intOfNat NatOne (unary_e1_closed unary_empty)))
        (intOfNat (BEDC.Derived.IntUp.natToUnary m)
          (BEDC.Derived.IntUp.natToUnary_unary m)) :=
    intMul_one_right
      (intOfNat (BEDC.Derived.IntUp.natToUnary m)
        (BEDC.Derived.IntUp.natToUnary_unary m))
  have rightId :
      IntEq
        (IntMul
          (intOfNat (BEDC.Derived.IntUp.natToUnary n)
            (BEDC.Derived.IntUp.natToUnary_unary n))
          (intOfNat NatOne (unary_e1_closed unary_empty)))
        (intOfNat (BEDC.Derived.IntUp.natToUnary n)
          (BEDC.Derived.IntUp.natToUnary_unary n)) :=
    intMul_one_right
      (intOfNat (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary_unary n))
  exact intLt_respects (IntEq_symm leftId) (IntEq_symm rightId)
    (intLt_nat_of_lt m n h)

theorem ratNat_apart0_of_pos {n : Nat} (h : 0 < n) :
    ratApart0 (ratNat n) :=
  ratApart0_of_pos (ratNat_pos_of_pos h)

private theorem natLeBool_true_to_le {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact Nat.succ_le_succ (ih h)

theorem ratLeBool_true_to_ratLe {x y : Rat} :
    ratLeBool x y = true -> ratLe x y := by
  intro h
  unfold ratLeBool at h
  unfold ratLe BEDC.Derived.RationalUp.intLe
  exact BEDC.Derived.IntUp.pairLe_of_length_order
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (natLeBool_true_to_le h)

theorem ratDivApart_mul_cancel {a b : Rat}
    (hb : ratApart0 b) :
    RatEq (ratMul (ratDivApart a b hb) b) a :=
  ratDivApart_mul_cancel_right hb

theorem ratMul_right_cancel_apart0 (x y c : Rat)
    (hc : ratApart0 c)
    (h : RatEq (ratMul x c) (ratMul y c)) :
    RatEq x y := by
  have invLeft :
      RatEq
        (ratMul (ratMul x c) (ratInvApart c hc))
        x := by
    exact RatEq_trans _ _ _
      (ratMul_assoc x c (ratInvApart c hc))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl x) (ratInvApart_mul c hc))
        (ratMul_one_right x))
  have invRight :
      RatEq
        (ratMul (ratMul y c) (ratInvApart c hc))
        y := by
    exact RatEq_trans _ _ _
      (ratMul_assoc y c (ratInvApart c hc))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl y) (ratInvApart_mul c hc))
        (ratMul_one_right y))
  exact RatEq_trans _ _ _
    (RatEq_symm invLeft)
    (RatEq_trans _ _ _
      (ratMul_respects h (RatEq_refl (ratInvApart c hc)))
      invRight)

theorem ratPow_apart0 {x : Rat}
    (hx : ratApart0 x) :
    ∀ n : Nat, ratApart0 (ratPow x n)
  | 0 => ratOne_apart
  | Nat.succ n => ratMul_apart0 (ratPow_apart0 hx n) hx

private theorem intOfNat_nat_add (m n : Nat) :
    IntEq
      (IntAdd
        (intOfNat (BEDC.Derived.IntUp.natToUnary m)
          (BEDC.Derived.IntUp.natToUnary_unary m))
        (intOfNat (BEDC.Derived.IntUp.natToUnary n)
          (BEDC.Derived.IntUp.natToUnary_unary n)))
      (intOfNat (BEDC.Derived.IntUp.natToUnary (m + n))
        (BEDC.Derived.IntUp.natToUnary_unary (m + n))) := by
  unfold IntEq
  have hpair :
      BEDC.Derived.IntUp.IntPairClassifier
        (BEDC.Derived.IntUp.pairAdd
          (intToPair (intOfNat (BEDC.Derived.IntUp.natToUnary m)
            (BEDC.Derived.IntUp.natToUnary_unary m)))
          (intToPair (intOfNat (BEDC.Derived.IntUp.natToUnary n)
            (BEDC.Derived.IntUp.natToUnary_unary n))))
        (intToPair (intOfNat (BEDC.Derived.IntUp.natToUnary (m + n))
          (BEDC.Derived.IntUp.natToUnary_unary (m + n)))) := by
    apply IntPairClassifier_of_length_eq
    · exact BEDC.Derived.IntUp.pairAdd_carrier
        (intToPair_carrier _) (intToPair_carrier _)
    · exact intToPair_carrier _
    change
      bwordLength (BEDC.FKernel.ExternalBinary.append
        (BEDC.Derived.IntUp.natToUnary m)
        (BEDC.Derived.IntUp.natToUnary n)) + bwordLength BHist.Empty =
      bwordLength (BEDC.Derived.IntUp.natToUnary (m + n)) +
        bwordLength (BEDC.FKernel.ExternalBinary.append BHist.Empty BHist.Empty)
    rw [BEDC.FKernel.ExternalBinary.bwordLength_append]
    rw [BEDC.FKernel.ExternalBinary.bwordLength_append]
    rw [BEDC.Derived.IntUp.natToUnary_length]
    rw [BEDC.Derived.IntUp.natToUnary_length]
    rw [BEDC.Derived.IntUp.natToUnary_length]
    change m + n + 0 = m + n + (0 + 0)
    rfl
  exact BEDC.Derived.IntUp.IntPairClassifier_equivalence_fields.right.right.right.right.left
    (BEDC.Derived.RationalUp.intAdd_pair_classifier
      (intOfNat (BEDC.Derived.IntUp.natToUnary m)
        (BEDC.Derived.IntUp.natToUnary_unary m))
      (intOfNat (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary_unary n)))
    hpair

theorem ratNat_add (m n : Nat) :
    RatEq (ratAdd (ratNat m) (ratNat n)) (ratNat (m + n)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratAdd ratNat intToRat
    change IntEq
      (IntAdd
        (IntMul
          (intOfNat (BEDC.Derived.IntUp.natToUnary m)
            (BEDC.Derived.IntUp.natToUnary_unary m))
          (intOfNat NatOne (unary_e1_closed unary_empty)))
        (IntMul
          (intOfNat (BEDC.Derived.IntUp.natToUnary n)
            (BEDC.Derived.IntUp.natToUnary_unary n))
          (intOfNat NatOne (unary_e1_closed unary_empty))))
      (intOfNat (BEDC.Derived.IntUp.natToUnary (m + n))
        (BEDC.Derived.IntUp.natToUnary_unary (m + n)))
    have leftId :
        IntEq
          (IntMul
            (intOfNat (BEDC.Derived.IntUp.natToUnary m)
              (BEDC.Derived.IntUp.natToUnary_unary m))
            (intOfNat NatOne (unary_e1_closed unary_empty)))
          (intOfNat (BEDC.Derived.IntUp.natToUnary m)
            (BEDC.Derived.IntUp.natToUnary_unary m)) :=
      intMul_one_right _
    have rightId :
        IntEq
          (IntMul
            (intOfNat (BEDC.Derived.IntUp.natToUnary n)
              (BEDC.Derived.IntUp.natToUnary_unary n))
            (intOfNat NatOne (unary_e1_closed unary_empty)))
          (intOfNat (BEDC.Derived.IntUp.natToUnary n)
            (BEDC.Derived.IntUp.natToUnary_unary n)) :=
      intMul_one_right _
    exact IntEq_trans
      (BEDC.Derived.RationalUp.IntAdd_respects leftId rightId)
      (intOfNat_nat_add m n)
  · unfold ratAdd ratNat intToRat ratDenInt
    change IntEq
      (intOfNat (BEDC.Derived.IntUp.natMulFn NatOne NatOne)
        (BEDC.Derived.IntUp.natMulFn_unary (unary_e1_closed unary_empty)
          (unary_e1_closed unary_empty)))
      (intOfNat NatOne (unary_e1_closed unary_empty))
    exact intOfNat_hsame_congr _ _
      (BEDC.Derived.PrimeUp.NatMul_unit_left_hsame
        (unary_e1_closed unary_empty)
        (BEDC.Derived.IntUp.natMulFn_rel (unary_e1_closed unary_empty)
          (unary_e1_closed unary_empty)))

theorem ratNat_mul (m n : Nat) :
    RatEq (ratMul (ratNat m) (ratNat n)) (ratNat (m * n)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNat intToRat
    change IntEq
      (IntMul
        (intOfNat (BEDC.Derived.IntUp.natToUnary m)
          (BEDC.Derived.IntUp.natToUnary_unary m))
        (intOfNat (BEDC.Derived.IntUp.natToUnary n)
          (BEDC.Derived.IntUp.natToUnary_unary n)))
      (intOfNat (BEDC.Derived.IntUp.natToUnary (m * n))
        (BEDC.Derived.IntUp.natToUnary_unary (m * n)))
    have raw :
        IntEq
          (IntMul
            (intOfNat (BEDC.Derived.IntUp.natToUnary m)
              (BEDC.Derived.IntUp.natToUnary_unary m))
            (intOfNat (BEDC.Derived.IntUp.natToUnary n)
              (BEDC.Derived.IntUp.natToUnary_unary n)))
          (intOfNat
            (BEDC.Derived.IntUp.natMulFn
              (BEDC.Derived.IntUp.natToUnary m)
              (BEDC.Derived.IntUp.natToUnary n))
            (BEDC.Derived.IntUp.natMulFn_unary
              (BEDC.Derived.IntUp.natToUnary_unary m)
              (BEDC.Derived.IntUp.natToUnary_unary n))) :=
      IntEq_symm (intOfNat_natMul_as_intMul
        (BEDC.Derived.IntUp.natToUnary m)
        (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary_unary m)
        (BEDC.Derived.IntUp.natToUnary_unary n)
        (BEDC.Derived.IntUp.natMulFn_unary
          (BEDC.Derived.IntUp.natToUnary_unary m)
          (BEDC.Derived.IntUp.natToUnary_unary n)))
    exact IntEq_trans raw
      (intOfNat_hsame_congr _ _ (by
        have rel := BEDC.Derived.IntUp.natMulFn_rel
          (BEDC.Derived.IntUp.natToUnary_unary m)
          (BEDC.Derived.IntUp.natToUnary_unary n)
        have len :
            bwordLength (BEDC.Derived.IntUp.natMulFn
              (BEDC.Derived.IntUp.natToUnary m)
              (BEDC.Derived.IntUp.natToUnary n)) = m * n := by
          have rawLen := BEDC.Derived.PrimeUp.NatMul_bwordLength rel
          rw [BEDC.Derived.IntUp.natToUnary_length] at rawLen
          rw [BEDC.Derived.IntUp.natToUnary_length] at rawLen
          exact rawLen
        apply (BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
          (BEDC.Derived.IntUp.natMulFn_unary
            (BEDC.Derived.IntUp.natToUnary_unary m)
            (BEDC.Derived.IntUp.natToUnary_unary n))
          (BEDC.Derived.IntUp.natToUnary_unary (m * n))).mpr
        rw [len, BEDC.Derived.IntUp.natToUnary_length]))
  · unfold ratMul ratNat intToRat ratDenInt
    change IntEq
      (intOfNat (BEDC.Derived.IntUp.natMulFn NatOne NatOne)
        (BEDC.Derived.IntUp.natMulFn_unary (unary_e1_closed unary_empty)
          (unary_e1_closed unary_empty)))
      (intOfNat NatOne (unary_e1_closed unary_empty))
    exact intOfNat_hsame_congr _ _
      (BEDC.Derived.PrimeUp.NatMul_unit_left_hsame
        (unary_e1_closed unary_empty)
        (BEDC.Derived.IntUp.natMulFn_rel (unary_e1_closed unary_empty)
          (unary_e1_closed unary_empty)))

private theorem ratAdd_right_neg_cancel (x y : Rat) :
    RatEq (ratAdd (ratAdd x y) (ratNeg y)) x := by
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x y (ratNeg y))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x)
        (BEDC.Derived.LocatedReal.ratAdd_neg_local y))
      (ratAdd_zero_right x))

private theorem ratAdd_right_cancel_RatEq {x y c : Rat} :
    RatEq (ratAdd x c) (ratAdd y c) -> RatEq x y := by
  intro h
  have shifted :
      RatEq
        (ratAdd (ratAdd x c) (ratNeg c))
        (ratAdd (ratAdd y c) (ratNeg c)) :=
    ratAdd_respects h (RatEq_refl (ratNeg c))
  exact RatEq_trans _ _ _
    (RatEq_symm (ratAdd_right_neg_cancel x c))
    (RatEq_trans _ _ _ shifted (ratAdd_right_neg_cancel y c))

private theorem ratSub_add_cancel_right (x y : Rat) :
    RatEq (ratAdd (ratSub x y) y) x := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x (ratNeg y) y)
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x)
        (BEDC.Derived.LocatedReal.ratNeg_add_local y))
      (ratAdd_zero_right x))

private theorem ratNat_respects_nat_eq {a b : Nat}
    (h : a = b) :
    RatEq (ratNat a) (ratNat b) := by
  cases h
  exact RatEq_refl (ratNat a)

private theorem nat_sub_add_cancel_of_le_local {a b : Nat} :
    b ≤ a -> a - b + b = a := by
  induction b generalizing a with
  | zero =>
      intro _h
      rw [Nat.sub_zero, Nat.add_zero]
  | succ b ih =>
      intro h
      cases a with
      | zero =>
          cases h
      | succ a =>
          rw [Nat.succ_sub_succ, Nat.add_succ]
          exact congrArg Nat.succ (ih (Nat.le_of_succ_le_succ h))

private theorem nat_add_sub_cancel_right_local (a b : Nat) :
    a + b - b = a := by
  induction b with
  | zero =>
      rw [Nat.add_zero, Nat.sub_zero]
  | succ b ih =>
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact ih

theorem ratNat_sub_of_le {a b : Nat} (h : b ≤ a) :
    RatEq (ratSub (ratNat a) (ratNat b)) (ratNat (a - b)) := by
  apply ratAdd_right_cancel_RatEq (c := ratNat b)
  exact RatEq_trans _ _ _
    (ratSub_add_cancel_right (ratNat a) (ratNat b))
    (RatEq_symm
      (RatEq_trans _ _ _
        (ratNat_add (a - b) b)
        (ratNat_respects_nat_eq (nat_sub_add_cancel_of_le_local h))))

private theorem ratMul_neg_right (x y : Rat) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem ratMul_neg_left (x y : Rat) :
    RatEq (ratMul (ratNeg x) y) (ratNeg (ratMul x y)) := by
  exact RatEq_trans _ _ _
    (ratMul_comm (ratNeg x) y)
    (RatEq_trans _ _ _
      (ratMul_neg_right y x)
      (ratNeg_respects (ratMul_comm y x)))

theorem ratMul_sub_right (a b c : Rat) :
    RatEq (ratMul (ratSub a b) c)
      (ratSub (ratMul a c) (ratMul b c)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratMul_add_right a (ratNeg b) c)
    (ratAdd_respects (RatEq_refl (ratMul a c))
      (ratMul_neg_left b c))

def twice (x : Rat) : Rat :=
  ratMul ratTwo x

def atanhPart (z : Rat) (M : Nat) : Rat :=
  ratSum M (fun j => oddTerm z j)

def atanhFormalSeries (z : Rat) (K : Nat) : Rat :=
  twice (atanhPart z K)

def SeriesEnclosedFrom
    (s : Nat -> Rat)
    (M : Nat)
    (lo hi : Rat) : Prop :=
  ∀ K : Nat, ratLe lo (s (M + K)) ∧ ratLe (s (M + K)) hi

theorem ratSum_nonneg {f : Nat -> Rat}
    (h : ∀ j : Nat, ratLe ratZero (f j)) :
    ∀ K : Nat, ratLe ratZero (ratSum K f)
  | 0 => by
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | Nat.succ K => by
      change ratLe ratZero (ratAdd (ratSum K f) (f K))
      have left : ratLe (ratAdd ratZero ratZero) (ratAdd (ratSum K f) (f K)) := by
        exact ratAdd_le_add (ratSum_nonneg h K) (h K)
      exact ratLe_of_RatEq_left (ratZero_add_left ratZero) left

theorem ratLe_add_nonneg_right (x y : Rat)
    (hy : ratLe ratZero y) :
    ratLe x (ratAdd x y) := by
  have shifted : ratLe (ratAdd x ratZero) (ratAdd x y) := by
    exact BEDC.Derived.LocatedReal.ratLe_add_left_mono (x := x) hy
  exact ratLe_of_RatEq_left (RatEq_symm (ratAdd_zero_right x)) shifted

theorem ratMul_le_mul_left_nonneg (c a b : Rat)
    (hc : ratLe ratZero c)
    (hab : ratLe a b) :
    ratLe (ratMul c a) (ratMul c b) :=
  ratMul_le_mul_nonneg_left hab hc

theorem atanhPart_add_tail (z : Rat) (M K : Nat) :
    RatEq (atanhPart z (M + K))
      (ratAdd (atanhPart z M) (oddTail z M K)) := by
  induction K with
  | zero =>
      rw [Nat.add_zero]
      change RatEq (atanhPart z M)
        (ratAdd (atanhPart z M) ratZero)
      exact RatEq_symm (ratAdd_zero_right (atanhPart z M))
  | succ K ih =>
      rw [Nat.add_succ]
      change RatEq
        (ratAdd (ratSum (M + K) (fun j => oddTerm z j))
          (oddTerm z (M + K)))
        (ratAdd (atanhPart z M)
          (ratAdd (oddTail z M K) (oddTerm z (M + K))))
      have regroup :
          RatEq
            (ratAdd (ratAdd (atanhPart z M) (oddTail z M K))
              (oddTerm z (M + K)))
            (ratAdd (atanhPart z M)
              (ratAdd (oddTail z M K) (oddTerm z (M + K)))) :=
        BEDC.Derived.LocatedReal.ratAdd_assoc_local
          (atanhPart z M) (oddTail z M K) (oddTerm z (M + K))
      exact RatEq_trans _ _ _
        (ratAdd_respects ih (RatEq_refl (oddTerm z (M + K))))
        regroup

theorem oddTail_nonneg (z : Rat)
    (hz0 : ratLe ratZero z)
    (M K : Nat) :
    ratLe ratZero (oddTail z M K) := by
  unfold oddTail
  apply ratSum_nonneg
  intro j
  exact oddTerm_nonneg hz0 (M + j)

theorem atanh_full_enclosure
    (z : Rat)
    (hz0 : ratLe ratZero z)
    (hz1 : ratLt z ratOne)
    (M : Nat) :
    SeriesEnclosedFrom
      (atanhFormalSeries z)
      M
      (twice (atanhPart z M))
      (twice
        (ratAdd
          (atanhPart z M)
          (atanhTailBound z hz0 hz1 M))) := by
  intro K
  have hsplit :
      RatEq (atanhPart z (M + K))
        (ratAdd (atanhPart z M) (oddTail z M K)) :=
    atanhPart_add_tail z M K
  have htail_nonneg :
      ratLe ratZero (oddTail z M K) :=
    oddTail_nonneg z hz0 M K
  have htail_le_bound :
      ratLe (oddTail z M K) (atanhTailBound z hz0 hz1 M) := by
    change ratLe (oddTail z M K) (oddTailBound z hz0 hz1 M)
    exact atanh_tail_kernel z hz0 hz1 M K
  have hpart_lo :
      ratLe (atanhPart z M) (atanhPart z (M + K)) :=
    ratLe_of_RatEq_right
      (ratLe_add_nonneg_right (atanhPart z M) (oddTail z M K)
        htail_nonneg)
      (RatEq_symm hsplit)
  have hpart_hi :
      ratLe
        (atanhPart z (M + K))
        (ratAdd (atanhPart z M) (atanhTailBound z hz0 hz1 M)) :=
    ratLe_of_RatEq_left hsplit
      (BEDC.Derived.LocatedReal.ratLe_add_left_mono
        (x := atanhPart z M) htail_le_bound)
  have hlo :
      ratLe
        (twice (atanhPart z M))
        (twice (atanhPart z (M + K))) := by
    unfold twice
    exact ratMul_le_mul_left_nonneg ratTwo
      (atanhPart z M)
      (atanhPart z (M + K))
      ratTwo_nonneg
      hpart_lo
  have hhi :
      ratLe
        (twice (atanhPart z (M + K)))
        (twice
          (ratAdd
            (atanhPart z M)
            (atanhTailBound z hz0 hz1 M))) := by
    unfold twice
    exact ratMul_le_mul_left_nonneg ratTwo
      (atanhPart z (M + K))
      (ratAdd (atanhPart z M) (atanhTailBound z hz0 hz1 M))
      ratTwo_nonneg
      hpart_hi
  exact And.intro hlo hhi

def zNum (N : Nat) : Rat :=
  ratNat (N - 1)

def zDen (N : Nat) : Rat :=
  ratNat (N + 1)

theorem zDen_pos (N : Nat) :
    ratLt ratZero (zDen N) := by
  unfold zDen
  exact ratNat_pos_of_pos (Nat.succ_pos N)

theorem zDen_apart0 (N : Nat) :
    ratApart0 (zDen N) :=
  ratApart0_of_pos (zDen_pos N)

def zOfNat (N : Nat) : Rat :=
  ratDivApart (zNum N) (zDen N) (zDen_apart0 N)

theorem zOfNat_nonneg
    {N : Nat}
    (_hN : 1 ≤ N) :
    ratLe ratZero (zOfNat N) := by
  unfold zOfNat
  have hnum : ratLe ratZero (zNum N) := by
    unfold zNum
    exact ratNat_nonneg (N - 1)
  exact ratDivApart_nonneg_of_nonneg_pos hnum (zDen_pos N) (zDen_apart0 N)

theorem zOfNat_lt_one
    {N : Nat}
    (_hN : 1 ≤ N) :
    ratLt (zOfNat N) ratOne := by
  unfold zOfNat
  have hden_pos : ratLt ratZero (zDen N) :=
    zDen_pos N
  have hcancel :
      RatEq
        (ratMul (ratDivApart (zNum N) (zDen N) (zDen_apart0 N))
          (zDen N))
        (zNum N) :=
    ratDivApart_mul_cancel_right (zDen_apart0 N)
  have hnum_lt_den : ratLt (zNum N) (zDen N) := by
    unfold zNum zDen
    exact ratNat_lt_of_nat_lt
      (Nat.lt_of_le_of_lt (Nat.sub_le N 1) (Nat.lt_succ_self N))
  apply ratLe_not_le_to_ratLt
  · have productLe :
        ratLe
          (ratMul
            (ratDivApart (zNum N) (zDen N) (zDen_apart0 N))
            (zDen N))
          (ratMul ratOne (zDen N)) :=
      ratLe_of_RatEq_left hcancel
        (ratLe_of_RatEq_right
          (ratLt_to_ratLe hnum_lt_den)
          (RatEq_symm (ratOne_mul_left (zDen N))))
    exact ratMul_le_cancel_right hden_pos productLe
  · intro oneLeZ
    have prodLe :
        ratLe (ratMul ratOne (zDen N))
          (ratMul
            (ratDivApart (zNum N) (zDen N) (zDen_apart0 N))
            (zDen N)) :=
      ratMul_le_mul_right oneLeZ (ratLt_to_ratLe hden_pos)
    have denLeNum :
        ratLe (zDen N) (zNum N) :=
      ratLe_of_RatEq_left (RatEq_symm (ratOne_mul_left (zDen N)))
        (ratLe_of_RatEq_right prodLe hcancel)
    exact ratLt_not_ratLe_reverse hnum_lt_den denLeNum

theorem one_sub_zOfNat_apart0
    {N : Nat}
    (hN : 1 ≤ N) :
    ratApart0 (ratSub ratOne (zOfNat N)) :=
  ratApart0_of_pos (sub_pos_of_lt (zOfNat_lt_one hN))

theorem one_add_zOfNat_mul_zDen
    {N : Nat}
    (_hN : 1 ≤ N) :
    RatEq (ratMul (ratAdd ratOne (zOfNat N)) (zDen N))
      (ratAdd (zDen N) (zNum N)) := by
  unfold zOfNat
  exact RatEq_trans _ _ _
    (ratMul_add_right ratOne
      (ratDivApart (zNum N) (zDen N) (zDen_apart0 N)) (zDen N))
    (ratAdd_respects (ratOne_mul_left (zDen N))
      (ratDivApart_mul_cancel (zDen_apart0 N)))

theorem one_sub_zOfNat_mul_zDen
    {N : Nat}
    (_hN : 1 ≤ N) :
    RatEq (ratMul (ratSub ratOne (zOfNat N)) (zDen N))
      (ratSub (zDen N) (zNum N)) := by
  unfold zOfNat
  exact RatEq_trans _ _ _
    (ratMul_sub_right ratOne
      (ratDivApart (zNum N) (zDen N) (zDen_apart0 N)) (zDen N))
    (ratAdd_respects (ratOne_mul_left (zDen N))
      (ratNeg_respects (ratDivApart_mul_cancel (zDen_apart0 N))))

private theorem nat_succ_sub_pred_eq_two
    {N : Nat}
    (hN : 1 ≤ N) :
    (N + 1) - (N - 1) = 2 := by
  cases N with
  | zero => cases hN
  | succ n =>
      change n + 2 - n = 2
      rw [Nat.add_comm n 2]
      exact nat_add_sub_cancel_right_local 2 n

private theorem nat_succ_add_pred_eq_mul_gap
    {N : Nat}
    (hN : 1 ≤ N) :
    ((N + 1) + (N - 1)) =
      N * ((N + 1) - (N - 1)) := by
  cases N with
  | zero => cases hN
  | succ n =>
      change n + 1 + 1 + n = (n + 1) * (n + 1 + 1 - n)
      have diff : n + 1 + 1 - n = 2 := by
        change n + 2 - n = 2
        rw [Nat.add_comm n 2]
        exact nat_add_sub_cancel_right_local 2 n
      rw [diff]
      rw [Nat.mul_succ]
      rw [Nat.mul_one]
      rw [Nat.add_assoc]
      rw [Nat.add_comm 1 n]

theorem zDen_add_zNum_eq_nat_mul_sub
    {N : Nat}
    (hN : 1 ≤ N) :
    RatEq (ratAdd (zDen N) (zNum N))
      (ratMul (ratNat N) (ratSub (zDen N) (zNum N))) := by
  unfold zDen zNum
  have left :
      RatEq (ratAdd (ratNat (N + 1)) (ratNat (N - 1)))
        (ratNat ((N + 1) + (N - 1))) :=
    ratNat_add (N + 1) (N - 1)
  have diff :
      RatEq (ratSub (ratNat (N + 1)) (ratNat (N - 1)))
        (ratNat ((N + 1) - (N - 1))) :=
    ratNat_sub_of_le
      (Nat.le_trans (Nat.sub_le N 1) (Nat.le_succ N))
  have right1 :
      RatEq
        (ratMul (ratNat N)
          (ratSub (ratNat (N + 1)) (ratNat (N - 1))))
        (ratMul (ratNat N)
          (ratNat ((N + 1) - (N - 1)))) :=
    ratMul_respects (RatEq_refl (ratNat N)) diff
  have right2 :
      RatEq
        (ratMul (ratNat N)
          (ratNat ((N + 1) - (N - 1))))
        (ratNat (N * ((N + 1) - (N - 1)))) :=
    ratNat_mul N ((N + 1) - (N - 1))
  have natLeft :
      ((N + 1) + (N - 1)) =
        N * ((N + 1) - (N - 1)) := by
    exact nat_succ_add_pred_eq_mul_gap hN
  exact RatEq_trans _ _ _ left
    (RatEq_trans _ _ _
      (by
        rw [natLeft]
        exact RatEq_refl _)
      (RatEq_symm (RatEq_trans _ _ _ right1 right2)))

theorem one_add_zOfNat_eq_nat_mul_one_sub
    {N : Nat}
    (hN : 1 ≤ N) :
    RatEq (ratAdd ratOne (zOfNat N))
      (ratMul (ratNat N) (ratSub ratOne (zOfNat N))) := by
  apply ratMul_right_cancel_apart0
    (ratAdd ratOne (zOfNat N))
    (ratMul (ratNat N) (ratSub ratOne (zOfNat N)))
    (zDen N)
    (zDen_apart0 N)
  have left :
      RatEq
        (ratMul (ratAdd ratOne (zOfNat N)) (zDen N))
        (ratAdd (zDen N) (zNum N)) :=
    one_add_zOfNat_mul_zDen hN
  have subClear :
      RatEq
        (ratMul (ratSub ratOne (zOfNat N)) (zDen N))
        (ratSub (zDen N) (zNum N)) :=
    one_sub_zOfNat_mul_zDen hN
  have right :
      RatEq
        (ratMul
          (ratMul (ratNat N) (ratSub ratOne (zOfNat N)))
          (zDen N))
        (ratMul (ratNat N) (ratSub (zDen N) (zNum N))) := by
    exact RatEq_trans _ _ _
      (ratMul_assoc (ratNat N) (ratSub ratOne (zOfNat N)) (zDen N))
      (ratMul_respects (RatEq_refl (ratNat N)) subClear)
  exact RatEq_trans _ _ _ left
    (RatEq_trans _ _ _
      (zDen_add_zNum_eq_nat_mul_sub hN)
      (RatEq_symm right))

theorem lnZ_bridge_rat
    {N : Nat}
    (hN : 1 ≤ N) :
    RatEq
      (ratDivApart
        (ratAdd ratOne (zOfNat N))
        (ratSub ratOne (zOfNat N))
        (one_sub_zOfNat_apart0 hN))
      (ratNat N) := by
  apply ratMul_right_cancel_apart0
    (ratDivApart
      (ratAdd ratOne (zOfNat N))
      (ratSub ratOne (zOfNat N))
      (one_sub_zOfNat_apart0 hN))
    (ratNat N)
    (ratSub ratOne (zOfNat N))
    (one_sub_zOfNat_apart0 hN)
  exact RatEq_trans _ _ _
    (ratDivApart_mul_cancel (one_sub_zOfNat_apart0 hN))
    (one_add_zOfNat_eq_nat_mul_one_sub hN)

def lnLo (N M : Nat) : Rat :=
  twice (atanhPart (zOfNat N) M)

def lnHi
    (N M : Nat)
    (hN : 1 ≤ N) : Rat :=
  twice
    (ratAdd
      (atanhPart (zOfNat N) M)
      (atanhTailBound
        (zOfNat N)
        (zOfNat_nonneg hN)
        (zOfNat_lt_one hN)
        M))

def lnWidth
    (N M : Nat)
    (hN : 1 ≤ N) : Rat :=
  twice
    (atanhTailBound
      (zOfNat N)
      (zOfNat_nonneg hN)
      (zOfNat_lt_one hN)
      M)

def lnWidthRad : Rat :=
  ratDivApart ratOne (ratPow (ratNat 10) 16)
    (ratPow_apart0 (ratNat_apart0_of_pos (by decide)) 16)

def lnM96 : Nat -> Nat
  | 1 => 0
  | 2 => 16
  | 3 => 24
  | 4 => 33
  | 5 => 42
  | 6 => 50
  | 7 => 58
  | 8 => 67
  | 9 => 75
  | 10 => 84
  | 11 => 92
  | 12 => 100
  | 13 => 109
  | 14 => 117
  | 15 => 125
  | 16 => 134
  | 17 => 142
  | 18 => 150
  | 19 => 159
  | 20 => 167
  | 21 => 175
  | 22 => 184
  | 23 => 192
  | 24 => 200
  | 25 => 209
  | 26 => 217
  | 27 => 225
  | 28 => 234
  | 29 => 242
  | 30 => 250
  | 31 => 259
  | 32 => 267
  | 33 => 275
  | 34 => 284
  | 35 => 292
  | 36 => 300
  | 37 => 309
  | 38 => 317
  | 39 => 325
  | 40 => 334
  | 41 => 342
  | 42 => 350
  | 43 => 359
  | 44 => 367
  | 45 => 375
  | 46 => 384
  | 47 => 392
  | 48 => 400
  | 49 => 409
  | 50 => 417
  | 51 => 425
  | 52 => 434
  | 53 => 442
  | 54 => 450
  | 55 => 459
  | 56 => 467
  | 57 => 475
  | 58 => 484
  | 59 => 492
  | 60 => 500
  | 61 => 509
  | 62 => 517
  | 63 => 525
  | 64 => 534
  | 65 => 542
  | 66 => 550
  | 67 => 559
  | 68 => 567
  | 69 => 575
  | 70 => 584
  | 71 => 592
  | 72 => 600
  | 73 => 609
  | 74 => 617
  | 75 => 625
  | 76 => 634
  | 77 => 642
  | 78 => 650
  | 79 => 659
  | 80 => 667
  | 81 => 675
  | 82 => 684
  | 83 => 692
  | 84 => 700
  | 85 => 709
  | 86 => 717
  | 87 => 725
  | 88 => 734
  | 89 => 742
  | 90 => 750
  | 91 => 759
  | 92 => 767
  | 93 => 775
  | 94 => 784
  | 95 => 792
  | 96 => 800
  | _ => 800

theorem formal_lnN_enclosure
    (N M : Nat)
    (hN : 1 ≤ N) :
    SeriesEnclosedFrom
      (fun K => atanhFormalSeries (zOfNat N) K)
      M
      (lnLo N M)
      (lnHi N M hN) := by
  unfold lnLo lnHi
  exact atanh_full_enclosure
    (zOfNat N)
    (zOfNat_nonneg hN)
    (zOfNat_lt_one hN)
    M

theorem formal_lnN96_enclosure
    (N : Nat)
    (hN1 : 1 ≤ N)
    (_hN96 : N ≤ 96) :
    SeriesEnclosedFrom
      (fun K => atanhFormalSeries (zOfNat N) K)
      (lnM96 N)
      (lnLo N (lnM96 N))
      (lnHi N (lnM96 N) hN1) := by
  exact formal_lnN_enclosure N (lnM96 N) hN1

inductive RatNumLnRealBridgeObligation : Type
  | analyticLogBridge

end BEDC.Real.RatNumLogEnclosure
