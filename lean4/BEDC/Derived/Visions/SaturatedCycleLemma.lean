import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

/-!
# Saturated cycle witness

This module records the minimal rational witness behind the saturated-cycle
obstruction used by the self-substitution RP no-go route.

Scope: the formal content is the concrete holonomy `-1` three-cycle Gram
matrix and its negative quadratic direction. The general `h ≠ 1` cycle theorem
and finite-exposure bridge are not claimed here. This is not RH evidence.
-/

namespace BEDC.Derived.Visions

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

/-- Tiny rational literal adapter for the displayed denominator-one constants in this file. -/
def satRpQ (n : Int) (d : Nat) : RatNum :=
  match n, d with
  | Int.ofNat 0, Nat.succ Nat.zero => ratZero
  | Int.ofNat 1, Nat.succ Nat.zero => ratOne
  | Int.ofNat 2, Nat.succ Nat.zero => ratTwo
  | Int.ofNat 4, Nat.succ Nat.zero => ratFour
  | Int.negSucc 0, Nat.succ Nat.zero => ratNeg ratOne
  | Int.negSucc 1, Nat.succ Nat.zero => ratNeg ratTwo
  | Int.negSucc 3, Nat.succ Nat.zero => ratNeg ratFour
  | _, _ => ratZero

def cycleGramMinusOne : List (List RatNum) :=
  [[satRpQ 1 1, satRpQ 1 1, satRpQ (-1) 1],
    [satRpQ 1 1, satRpQ 1 1, satRpQ 1 1],
    [satRpQ (-1) 1, satRpQ 1 1, satRpQ 1 1]]

def satCycleWitness : List RatNum :=
  [satRpQ 1 1, satRpQ (-2) 1, satRpQ 1 1]

/-- The displayed matrix-vector product `G * w = (-2, 0, -2)`. -/
def satCycleGramTimesWitness : List RatNum :=
  [satRpQ (-2) 1, satRpQ 0 1, satRpQ (-2) 1]

def satCycleQuadForm : RatNum :=
  ratAdd
    (ratAdd
      (ratMul (satRpQ 1 1) (satRpQ (-2) 1))
      (ratMul (satRpQ (-2) 1) (satRpQ 0 1)))
    (ratMul (satRpQ 1 1) (satRpQ (-2) 1))

def SaturatedCycleNegativeDirection
    (gram : List (List RatNum)) (w : List RatNum) (q : RatNum) : Prop :=
  gram = cycleGramMinusOne ∧
    w = satCycleWitness ∧
      RatEq q satCycleQuadForm ∧ ratLt q ratZero

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

private theorem ratMul_zero_left_local (x : RatNum) :
    RatEq (ratMul ratZero x) ratZero := by
  apply ratNum_zero_to_RatEq_zero
  unfold ratMul ratZero intToRat
  change IntEq (IntMul intZero x.num) intZero
  exact intMul_zero_left x.num

private theorem ratMul_zero_right_local (x : RatNum) :
    RatEq (ratMul x ratZero) ratZero := by
  exact RatEq_trans _ _ _
    (ratMul_comm x ratZero)
    (ratMul_zero_left_local x)

private theorem ratNeg_zero_local :
    RatEq (ratNeg ratZero) ratZero := by
  apply ratEq_of_num_den_intEq
  · unfold ratNeg ratZero intToRat
    exact BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_zero
  · unfold ratNeg ratZero ratDenInt intToRat
    exact IntEq_refl _

private theorem ratLe_neg_anti_local {a b : RatNum} :
    ratLe a b -> ratLe (ratNeg b) (ratNeg a) := by
  intro h
  let t := ratAdd (ratNeg a) (ratNeg b)
  have shifted : ratLe (ratAdd a t) (ratAdd b t) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := a) (x' := b) (y := t) h
  have leftEq : RatEq (ratAdd a t) (ratNeg b) := by
    unfold t
    exact RatEq_trans _ _ _
      (RatEq_symm
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local
          a (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (ratAdd_respects
          (BEDC.Derived.LocatedReal.ratAdd_neg_local a)
          (RatEq_refl (ratNeg b)))
        (ratZero_add_left (ratNeg b)))
  have rightEq : RatEq (ratAdd b t) (ratNeg a) := by
    unfold t
    exact RatEq_trans _ _ _
      (ratAdd_respects
        (RatEq_refl b)
        (ratAdd_comm (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local
            b (ratNeg b) (ratNeg a)))
        (RatEq_trans _ _ _
          (ratAdd_respects
            (BEDC.Derived.LocatedReal.ratAdd_neg_local b)
            (RatEq_refl (ratNeg a)))
          (ratZero_add_left (ratNeg a))))
  exact ratLe_respects leftEq rightEq shifted

private theorem ratLt_neg_anti_local {a b : RatNum} :
    ratLt a b -> ratLt (ratNeg b) (ratNeg a) := by
  intro h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_neg_anti_local (ratLt_to_ratLe h)
  · intro reverse
    have raw : ratLe (ratNeg (ratNeg b)) (ratNeg (ratNeg a)) :=
      ratLe_neg_anti_local reverse
    have ba : ratLe b a :=
      ratLe_respects
        (BEDC.Derived.LocatedReal.ratNeg_neg_local b)
        (BEDC.Derived.LocatedReal.ratNeg_neg_local a)
        raw
    exact ratLt_not_ratLe_reverse h ba

theorem sat_cycle_quad_form_eq_neg_four :
    RatEq satCycleQuadForm (satRpQ (-4) 1) := by
  unfold satCycleQuadForm
  change
    RatEq
      (ratAdd
        (ratAdd
          (ratMul ratOne (ratNeg ratTwo))
          (ratMul (ratNeg ratTwo) ratZero))
        (ratMul ratOne (ratNeg ratTwo)))
      (ratNeg ratFour)
  have first :
      RatEq (ratMul ratOne (ratNeg ratTwo)) (ratNeg ratTwo) :=
    ratOne_mul_left (ratNeg ratTwo)
  have middle :
      RatEq (ratMul (ratNeg ratTwo) ratZero) ratZero :=
    ratMul_zero_right_local (ratNeg ratTwo)
  have collapsed :
      RatEq
        (ratAdd
          (ratAdd
            (ratMul ratOne (ratNeg ratTwo))
            (ratMul (ratNeg ratTwo) ratZero))
          (ratMul ratOne (ratNeg ratTwo)))
        (ratAdd (ratNeg ratTwo) (ratNeg ratTwo)) := by
    exact RatEq_trans _ _ _
      (ratAdd_respects (ratAdd_respects first middle) first)
      (ratAdd_respects (ratAdd_zero_right (ratNeg ratTwo))
        (RatEq_refl (ratNeg ratTwo)))
  exact RatEq_trans _ _ _ collapsed
    (by
      unfold ratFour
      exact RatEq_symm
        (BEDC.Derived.LocatedReal.ratNeg_add_dist_local ratTwo ratTwo))

theorem sat_cycle_quad_form_negative :
    ratLt satCycleQuadForm ratZero := by
  apply ratLt_of_RatEq_left sat_cycle_quad_form_eq_neg_four
  change ratLt (ratNeg ratFour) ratZero
  have negStep : ratLt (ratNeg ratFour) (ratNeg ratZero) :=
    ratLt_neg_anti_local ratFour_pos
  exact ratLt_of_RatEq_right negStep ratNeg_zero_local

theorem saturated_cycle_gram_not_psd :
    ∃ w : List RatNum, ∃ q : RatNum,
      w = satCycleWitness ∧
        SaturatedCycleNegativeDirection cycleGramMinusOne w q := by
  exact
    ⟨satCycleWitness, satCycleQuadForm, rfl,
      rfl, rfl, RatEq_refl satCycleQuadForm, sat_cycle_quad_form_negative⟩

end BEDC.Derived.Visions
