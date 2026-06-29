import BEDC.Derived.LocatedReal.GroundedToleranceKit
import BEDC.Real.RatNumKernel

namespace BEDC.Derived.LocatedReal

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.RationalUp

private abbrev RatInt : Type :=
  BEDC.Derived.PrimeUp.IntegerUp

def halfPow (k : Nat) : Rat :=
  dyadicRat k

private theorem nat_right_distrib_local (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := Nat.mul_comm (a + b) c
    _ = c * a + c * b := Nat.left_distrib c a b
    _ = a * c + c * b := congrArg (fun t => t + c * b) (Nat.mul_comm c a)
    _ = a * c + b * c := congrArg (fun t => a * c + t) (Nat.mul_comm c b)

private def approxIntNat (n : Nat) : RatInt :=
  intOfNat (BEDC.Derived.IntUp.natToUnary n)
    (BEDC.Derived.IntUp.natToUnary_unary n)

private theorem intOne_eq_approxIntNat_one :
    IntEq intOne (approxIntNat 1) := by
  unfold approxIntNat intOne BEDC.Derived.PadicUp.NatOne
  exact IntEq_refl _

private theorem approxIntNat_add (a b : Nat) :
    IntEq (IntAdd (approxIntNat a) (approxIntNat b))
      (approxIntNat (a + b)) := by
  unfold approxIntNat IntAdd intAdd intOfNat IntEq intToPair
  change
    BEDC.Derived.IntUp.IntPairClassifier
      (intToPair
        (pairToInt
          (BEDC.Derived.IntUp.pairAdd
            (BEDC.Derived.IntUp.natToUnary a, BHist.Empty)
            (BEDC.Derived.IntUp.natToUnary b, BHist.Empty))))
      (BEDC.Derived.IntUp.natToUnary (a + b), BHist.Empty)
  exact BEDC.Derived.IntUp.IntPairClassifier_equivalence_fields.right.right.right.right.left
    (intToPair_pairToInt_classifier
      (BEDC.Derived.IntUp.pairAdd
        (BEDC.Derived.IntUp.natToUnary a, BHist.Empty)
        (BEDC.Derived.IntUp.natToUnary b, BHist.Empty))
      (BEDC.Derived.IntUp.pairAdd_carrier
        ⟨BEDC.Derived.IntUp.natToUnary_unary a, unary_empty⟩
        ⟨BEDC.Derived.IntUp.natToUnary_unary b, unary_empty⟩))
    (by
      apply IntPairClassifier_of_length_eq
      · exact BEDC.Derived.IntUp.pairAdd_carrier
          ⟨BEDC.Derived.IntUp.natToUnary_unary a, unary_empty⟩
          ⟨BEDC.Derived.IntUp.natToUnary_unary b, unary_empty⟩
      · exact ⟨BEDC.Derived.IntUp.natToUnary_unary (a + b), unary_empty⟩
      unfold BEDC.Derived.IntUp.pairAdd
      rw [BEDC.FKernel.ExternalBinary.bwordLength_append]
      rw [BEDC.Derived.IntUp.natToUnary_length]
      rw [BEDC.Derived.IntUp.natToUnary_length]
      rw [BEDC.Derived.IntUp.natToUnary_length]
      rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
      change a + b + 0 = a + b + 0
      rfl)

private theorem approxIntNat_mul (a b : Nat) :
    IntEq (IntMul (approxIntNat a) (approxIntNat b))
      (approxIntNat (a * b)) := by
  unfold approxIntNat
  have raw :=
    intOfNat_natMul_as_intMul
      (BEDC.Derived.IntUp.natToUnary a)
      (BEDC.Derived.IntUp.natToUnary b)
      (BEDC.Derived.IntUp.natToUnary_unary a)
      (BEDC.Derived.IntUp.natToUnary_unary b)
      (BEDC.Derived.IntUp.natMulFn_unary
        (BEDC.Derived.IntUp.natToUnary_unary a)
        (BEDC.Derived.IntUp.natToUnary_unary b))
  exact IntEq_trans (IntEq_symm raw)
    (by
      exact intOfNat_hsame_congr
        (BEDC.Derived.IntUp.natMulFn_unary
          (BEDC.Derived.IntUp.natToUnary_unary a)
          (BEDC.Derived.IntUp.natToUnary_unary b))
        (BEDC.Derived.IntUp.natToUnary_unary (a * b))
        (natMulFn_natToUnary_eq a b))

private theorem ratDenInt_halfPow (k : Nat) :
    IntEq (ratDenInt (halfPow k)) (approxIntNat (powTwoNat k)) := by
  unfold halfPow ratDenInt dyadicRat approxIntNat
  exact IntEq_refl _

private theorem halfPow_add_num (k : Nat) :
    IntEq (ratAdd (halfPow k) (halfPow k)).num
      (approxIntNat (powTwoNat k + powTwoNat k)) := by
  unfold halfPow ratAdd
  change
    IntEq
      (IntAdd
        (IntMul (dyadicRat k).num (ratDenInt (dyadicRat k)))
        (IntMul (dyadicRat k).num (ratDenInt (dyadicRat k))))
      (approxIntNat (powTwoNat k + powTwoNat k))
  have term :
      IntEq (IntMul (dyadicRat k).num (ratDenInt (dyadicRat k)))
        (approxIntNat (powTwoNat k)) := by
    exact IntEq_trans
      (IntMul_respects intOne_eq_approxIntNat_one (ratDenInt_halfPow k))
      (IntEq_trans (approxIntNat_mul 1 (powTwoNat k))
        (by
          change IntEq (approxIntNat (1 * powTwoNat k))
            (approxIntNat (powTwoNat k))
          rw [Nat.one_mul]
          exact IntEq_refl _))
  exact IntEq_trans (IntAdd_respects term term)
    (approxIntNat_add (powTwoNat k) (powTwoNat k))

private theorem halfPow_add_den (k : Nat) :
    IntEq (ratDenInt (ratAdd (halfPow k) (halfPow k)))
      (approxIntNat (powTwoNat k * powTwoNat k)) := by
  unfold halfPow
  exact IntEq_trans (ratDenInt_add (dyadicRat k) (dyadicRat k))
    (IntEq_trans
      (IntMul_respects (ratDenInt_halfPow k) (ratDenInt_halfPow k))
      (approxIntNat_mul (powTwoNat k) (powTwoNat k)))

private theorem halfPow_succ_nat_eq (k : Nat) :
    (powTwoNat (Nat.succ k) + powTwoNat (Nat.succ k)) * powTwoNat k =
      powTwoNat (Nat.succ k) * powTwoNat (Nat.succ k) := by
  change (2 * powTwoNat k + 2 * powTwoNat k) * powTwoNat k =
    (2 * powTwoNat k) * (2 * powTwoNat k)
  have twoE : 2 * powTwoNat k = powTwoNat k + powTwoNat k :=
    Nat.two_mul (powTwoNat k)
  calc
    (2 * powTwoNat k + 2 * powTwoNat k) * powTwoNat k =
        (2 * powTwoNat k) * powTwoNat k +
          (2 * powTwoNat k) * powTwoNat k := nat_right_distrib_local _ _ _
    _ = (2 * powTwoNat k) * (powTwoNat k + powTwoNat k) :=
        (Nat.left_distrib (2 * powTwoNat k) (powTwoNat k) (powTwoNat k)).symm
    _ = (2 * powTwoNat k) * (2 * powTwoNat k) :=
        congrArg (fun t => (2 * powTwoNat k) * t) twoE.symm

private theorem halfPow_succ_add_reverse_le (k : Nat) :
    ratLe (halfPow k)
      (ratAdd (halfPow (Nat.succ k)) (halfPow (Nat.succ k))) := by
  unfold ratLe
  have leftNorm :
      IntEq
        (IntMul (halfPow k).num
          (ratDenInt (ratAdd (halfPow (Nat.succ k)) (halfPow (Nat.succ k)))))
        (approxIntNat (powTwoNat (Nat.succ k) * powTwoNat (Nat.succ k))) := by
    exact IntEq_trans
      (IntMul_respects intOne_eq_approxIntNat_one (halfPow_add_den (Nat.succ k)))
      (IntEq_trans
        (approxIntNat_mul 1 (powTwoNat (Nat.succ k) * powTwoNat (Nat.succ k)))
        (by
          change IntEq
            (approxIntNat
              (1 * (powTwoNat (Nat.succ k) * powTwoNat (Nat.succ k))))
            (approxIntNat (powTwoNat (Nat.succ k) * powTwoNat (Nat.succ k)))
          rw [Nat.one_mul]
          exact IntEq_refl _))
  have rightNorm :
      IntEq
        (IntMul
          (ratAdd (halfPow (Nat.succ k)) (halfPow (Nat.succ k))).num
          (ratDenInt (halfPow k)))
        (approxIntNat
          ((powTwoNat (Nat.succ k) + powTwoNat (Nat.succ k)) * powTwoNat k)) := by
    exact IntEq_trans
      (IntMul_respects (halfPow_add_num (Nat.succ k)) (ratDenInt_halfPow k))
      (approxIntNat_mul
        (powTwoNat (Nat.succ k) + powTwoNat (Nat.succ k)) (powTwoNat k))
  exact intLe_respects (IntEq_symm leftNorm) (IntEq_symm rightNorm)
    (intOfNat_le_of_nat_le
      (BEDC.Derived.IntUp.natToUnary
        (powTwoNat (Nat.succ k) * powTwoNat (Nat.succ k)))
      (BEDC.Derived.IntUp.natToUnary
        ((powTwoNat (Nat.succ k) + powTwoNat (Nat.succ k)) * powTwoNat k))
      (BEDC.Derived.IntUp.natToUnary_unary _)
      (BEDC.Derived.IntUp.natToUnary_unary _)
      (by
        rw [BEDC.Derived.IntUp.natToUnary_length,
          BEDC.Derived.IntUp.natToUnary_length]
        exact Nat.le_of_eq (halfPow_succ_nat_eq k).symm))

theorem halfPow_nonneg (k : Nat) :
    ratLe ratZero (halfPow k) := by
  exact dyadic_nonneg k

theorem halfPow_pos (k : Nat) :
    ratLt ratZero (halfPow k) := by
  apply ratLe_not_le_to_ratLt
  · exact halfPow_nonneg k
  · intro reverse
    have zeroEq : RatEq (halfPow k) ratZero :=
      ratLe_antisymm reverse (halfPow_nonneg k)
    have numZero : IntEq intOne intZero := by
      have raw := RatEq_zero_num zeroEq
      unfold halfPow dyadicRat at raw
      exact raw
    have oneApart : intApart0 intOne := by
      unfold intApart0 intOne intOfNat
      exact Or.inr
        (BEDC.FKernel.Hist.hsame_refl BEDC.Derived.PadicUp.NatOne)
    exact intApart0_not_zero_pair
      oneApart numZero

theorem halfPow_succ_add (k : Nat) :
    RatEq (ratAdd (halfPow (Nat.succ k)) (halfPow (Nat.succ k)))
      (halfPow k) := by
  apply ratLe_antisymm
  · exact dyadic_succ_add k
  · exact halfPow_succ_add_reverse_le k

theorem halfPow_antitone {lo hi : Nat} :
    lo <= hi -> ratLe (halfPow hi) (halfPow lo) := by
  intro h
  exact dyadic_monotone h

def approxClose (x y : Rat) (k : Nat) : Prop :=
  ratLe (ratAbs (ratSub x y)) (halfPow k)

def approxApart (x y : Rat) (k : Nat) : Prop :=
  ratLt (halfPow k) (ratAbs (ratSub x y))

theorem approxClose_eq_tolerance (x y : Rat) (k : Nat) :
    approxClose x y k = ratToleranceClose x y k := by
  rfl

theorem approxClose_refl (x : Rat) (k : Nat) :
    approxClose x x k := by
  exact groundedRatToleranceLaws.close_refl x k

theorem approxClose_symm {x y : Rat} {k : Nat} :
    approxClose x y k -> approxClose y x k := by
  exact groundedRatToleranceLaws.close_symm

theorem approxClose_weaken {x y : Rat} {hi lo : Nat} :
    lo <= hi -> approxClose x y hi -> approxClose x y lo := by
  exact groundedRatToleranceLaws.close_weaken

theorem approxClose_triangle {x y z : Rat} {k : Nat} :
    approxClose x y (Nat.succ k) ->
      approxClose y z (Nat.succ k) ->
        approxClose x z k := by
  exact groundedRatToleranceLaws.close_triangle

theorem approxClose_of_RatEq {x y : Rat} :
    RatEq x y -> forall k : Nat, approxClose x y k := by
  exact groundedRatToleranceLaws.eq_close

theorem approxClose_add {x x' y y' : Rat} {k : Nat} :
    approxClose x x' (Nat.succ k) ->
      approxClose y y' (Nat.succ k) ->
        approxClose (ratAdd x y) (ratAdd x' y') k := by
  exact groundedRatToleranceLaws.add_close

theorem approxClose_neg {x y : Rat} {k : Nat} :
    approxClose x y k -> approxClose (ratNeg x) (ratNeg y) k := by
  exact groundedRatToleranceLaws.neg_close

theorem approxApart_symm {x y : Rat} {k : Nat} :
    approxApart x y k -> approxApart y x k := by
  intro h
  unfold approxApart at h ⊢
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right h
    (RatEq_trans _ _ _
      (RatEq_symm (ratDist_eq_abs_sub x y))
      (RatEq_trans _ _ _ (ratDist_symm x y) (ratDist_eq_abs_sub y x)))

def RatMetricKitApprox : RatMetricKit where
  close := approxClose
  apart := approxApart
  le := ratLe
  close_refl := approxClose_refl
  close_symm := by
    intro x y k
    exact approxClose_symm
  close_weaken := by
    intro x y hi lo
    exact approxClose_weaken
  close_triangle := by
    intro x y z k
    exact approxClose_triangle
  eq_close := by
    intro x y h
    exact approxClose_of_RatEq h
  add_close := by
    intro x x' y y' k
    exact approxClose_add
  neg_close := by
    intro x y k
    exact approxClose_neg
  le_refl := ratLe_refl
  le_trans := by
    intro x y z
    exact ratLe_trans
  le_antisymm := by
    intro x y
    exact ratLe_antisymm
  apart_symm := by
    intro x y k
    exact approxApart_symm

end BEDC.Derived.LocatedReal
