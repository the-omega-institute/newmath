import BEDC.Real.RatNumKernel
import BEDC.Derived.RHRoute.OCLSDReflectionForm

/-!
Finite radial-energy certificate for the multi-rotor route.

This file is only the finite algebraic kernel of the radial energy computation:
for a nonempty list of positive rational weights and positive rational log-values,
`delta^2 * C = 0` is equivalent to `delta = 0`, where `C` is the positive
window constant.  It is not RH.  The analytic implication
`PositiveRadialDefect(s) -> Apart_0(zeta(s))`, and the identification of these
rational log-values with real natural logarithms, remain in the paper and
completed-carrier layers.
-/

set_option maxHeartbeats 4000000

namespace BEDC.Derived.RHRoute.FiniteRadialEnergyCertificate

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.RHRoute.OCLSDReflectionForm

/-- One finite rotor channel: a positive weight and a positive log-value. -/
structure RadialWindowEntry where
  weight : RatNum
  logval : RatNum
  weight_pos : ratLt ratZero weight
  logval_pos : ratLt ratZero logval

/-- The positive window constant `sum w_p * ell_p^2`. -/
def windowConst : List RadialWindowEntry -> RatNum
  | [] => ratZero
  | entry :: rest =>
      ratAdd (ratMul entry.weight (ratMul entry.logval entry.logval))
        (windowConst rest)

/-- Finite radial energy `delta^2 * C_S`. -/
def radialEnergy (delta : RatNum) (S : List RadialWindowEntry) : RatNum :=
  ratMul (ratMul delta delta) (windowConst S)

private theorem ratLt_respects_local {x x' y y' : RatNum} :
    RatEq x x' -> RatEq y y' -> ratLt x y -> ratLt x' y' := by
  intro xx' yy' h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_respects xx' yy' (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_respects (RatEq_symm yy') (RatEq_symm xx') reverse)

private theorem ratAdd_right_neg_cancel_local (x y : RatNum) :
    RatEq (ratAdd (ratAdd x y) (ratNeg y)) x := by
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x y (ratNeg y))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x)
        (BEDC.Derived.LocatedReal.ratAdd_neg_local y))
      (ratAdd_zero_right x))

private theorem ratLe_add_right_cancel_local {x x' y : RatNum} :
    ratLe (ratAdd x y) (ratAdd x' y) -> ratLe x x' := by
  intro h
  have shifted :
      ratLe (ratAdd (ratAdd x y) (ratNeg y))
        (ratAdd (ratAdd x' y) (ratNeg y)) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := ratAdd x y) (x' := ratAdd x' y) (y := ratNeg y) h
  exact ratLe_respects
    (ratAdd_right_neg_cancel_local x y)
    (ratAdd_right_neg_cancel_local x' y)
    shifted

private theorem ratLt_add_right_mono_local {x x' y : RatNum} :
    ratLt x x' -> ratLt (ratAdd x y) (ratAdd x' y) := by
  intro h
  apply ratLe_not_le_to_ratLt
  · exact BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := x) (x' := x') (y := y) (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_add_right_cancel_local reverse)

private theorem ratAdd_pos_of_pos_nonneg {x y : RatNum} :
    ratLt ratZero x -> ratLe ratZero y -> ratLt ratZero (ratAdd x y) := by
  intro xPos yNonneg
  have raw : ratLt (ratAdd ratZero y) (ratAdd x y) :=
    ratLt_add_right_mono_local (x := ratZero) (x' := x) (y := y) xPos
  exact ratLe_lt_trans yNonneg
    (ratLt_respects_local (ratZero_add_left y) (RatEq_refl _) raw)

private theorem ratAdd_pos_of_pos_pos {x y : RatNum} :
    ratLt ratZero x -> ratLt ratZero y -> ratLt ratZero (ratAdd x y) := by
  intro hx hy
  exact ratAdd_pos_of_pos_nonneg hx (ratLt_to_ratLe hy)

private theorem ratMul_pos_of_pos_pos {x y : RatNum} :
    ratLt ratZero x -> ratLt ratZero y -> ratLt ratZero (ratMul x y) := by
  intro hx hy
  have raw : ratLt (ratMul x ratZero) (ratMul x y) :=
    ratMul_lt_mul_left hy hx
  exact ratLt_of_RatEq_left (RatEq_symm (ratMul_zero_right x)) raw

private theorem windowConst_nonneg (S : List RadialWindowEntry) :
    ratLe ratZero (windowConst S) := by
  induction S with
  | nil =>
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | cons entry rest ih =>
      change ratLe ratZero
        (ratAdd (ratMul entry.weight (ratMul entry.logval entry.logval))
          (windowConst rest))
      exact ratLe_of_RatEq_left
        (RatEq_symm (ratZero_add_left ratZero))
        (ratAdd_le_add
          (ratMul_nonneg (ratLt_to_ratLe entry.weight_pos)
            (ratSq_nonneg entry.logval))
          ih)

private theorem entryTerm_pos (entry : RadialWindowEntry) :
    ratLt ratZero (ratMul entry.weight (ratMul entry.logval entry.logval)) := by
  have logSqPos :
      ratLt ratZero (ratMul entry.logval entry.logval) :=
    ratMul_pos_of_pos_pos entry.logval_pos entry.logval_pos
  exact ratMul_pos_of_pos_pos entry.weight_pos logSqPos

/-- A nonempty finite positive window has a strictly positive constant. -/
theorem windowConst_pos (S : List RadialWindowEntry) (hne : S ≠ []) :
    ratLt ratZero (windowConst S) := by
  cases S with
  | nil =>
      exact False.elim (hne rfl)
  | cons entry rest =>
      change ratLt ratZero
        (ratAdd (ratMul entry.weight (ratMul entry.logval entry.logval))
          (windowConst rest))
      exact ratAdd_pos_of_pos_nonneg (entryTerm_pos entry)
        (windowConst_nonneg rest)

private theorem ratNeg_nonneg_of_nonpos {x : RatNum} :
    ratLe x ratZero -> ratLe ratZero (ratNeg x) := by
  intro h
  exact ratLe_of_RatEq_right (ratSub_nonneg_of_le h)
    (ratZero_add_left (ratNeg x))

private theorem ratMul_neg_right_local (x y : RatNum) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem ratNeg_mul_neg_local (x : RatNum) :
    RatEq (ratMul (ratNeg x) (ratNeg x)) (ratMul x x) :=
  RatEq_trans _ _ _ (ratMul_neg_right_local (ratNeg x) x)
    (RatEq_trans _ _ _
      (ratNeg_respects
        (RatEq_trans _ _ _ (ratMul_comm (ratNeg x) x)
          (ratMul_neg_right_local x x)))
      (BEDC.Derived.LocatedReal.ratNeg_neg_local (ratMul x x)))

private theorem ratNeg_zero_local :
    RatEq (ratNeg ratZero) ratZero :=
  RatEq_trans _ _ _
    (RatEq_symm (ratAdd_zero_right (ratNeg ratZero)))
    (BEDC.Derived.LocatedReal.ratNeg_add_local ratZero)

private theorem ratMul_self_pos_of_pos {x : RatNum} :
    ratLt ratZero x -> ratLt ratZero (ratMul x x) := by
  intro h
  exact ratMul_pos_of_pos_pos h h

private theorem ratMul_self_pos_of_neg {x : RatNum} :
    ratLt x ratZero -> ratLt ratZero (ratMul x x) := by
  intro h
  have negPos : ratLt ratZero (ratNeg x) := by
    have nonneg : ratLe ratZero (ratNeg x) :=
      ratNeg_nonneg_of_nonpos (ratLt_to_ratLe h)
    apply ratLe_not_le_to_ratLt
    · exact nonneg
    · intro nonpos
      have negZero : RatEq (ratNeg x) ratZero :=
        ratLe_antisymm nonpos nonneg
      have xZero : RatEq x ratZero := by
        exact RatEq_trans _ _ _
          (RatEq_symm (BEDC.Derived.LocatedReal.ratNeg_neg_local x))
          (RatEq_trans _ _ _
            (ratNeg_respects negZero)
            ratNeg_zero_local)
      exact ratLt_not_RatEq h xZero
  exact ratLt_of_RatEq_right
    (ratMul_self_pos_of_pos negPos)
    (ratNeg_mul_neg_local x)

private theorem ratMul_self_pos_of_ne_zero {x : RatNum} :
    (RatEq x ratZero -> False) -> ratLt ratZero (ratMul x x) := by
  intro hne
  cases BEDC.Derived.RationalOrderArithUp.rat_order_trichotomy x ratZero with
  | inl hneg =>
      exact ratMul_self_pos_of_neg hneg
  | inr rest =>
      cases rest with
      | inl hzero =>
          exact False.elim (hne hzero)
      | inr hpos =>
          exact ratMul_self_pos_of_pos hpos

private theorem ratMul_pos_cancel_right_zero {x c : RatNum} :
    ratLt ratZero c ->
      RatEq (ratMul x c) ratZero ->
        RatEq x ratZero := by
  intro hc hprod
  cases BEDC.Derived.RationalOrderArithUp.rat_order_trichotomy x ratZero with
  | inl xNeg =>
      have prodNeg : ratLt (ratMul x c) ratZero := by
        have raw : ratLt (ratMul x c) (ratMul ratZero c) :=
          ratMul_lt_mul_right xNeg hc
        exact ratLt_of_RatEq_right raw (ratMul_zero_left c)
      exact False.elim
        (ratLt_not_RatEq prodNeg hprod)
  | inr rest =>
      cases rest with
      | inl xZero =>
          exact xZero
      | inr xPos =>
          have prodPos : ratLt ratZero (ratMul x c) :=
            ratMul_pos_of_pos_pos xPos hc
          exact False.elim (ratLt_not_RatEq prodPos (RatEq_symm hprod))

private theorem ratMul_self_eq_zero_to_zero {x : RatNum} :
    RatEq (ratMul x x) ratZero -> RatEq x ratZero := by
  intro hsq
  cases BEDC.Derived.RationalOrderArithUp.rat_order_trichotomy x ratZero with
  | inl hneg =>
      exact False.elim
        (ratLt_not_RatEq (ratMul_self_pos_of_neg hneg) (RatEq_symm hsq))
  | inr rest =>
      cases rest with
      | inl hzero =>
          exact hzero
      | inr hpos =>
          exact False.elim
            (ratLt_not_RatEq (ratMul_self_pos_of_pos hpos) (RatEq_symm hsq))

private theorem ratMul_self_zero_of_zero {x : RatNum} :
    RatEq x ratZero -> RatEq (ratMul x x) ratZero := by
  intro h
  exact RatEq_trans _ _ _
    (ratMul_respects h h)
    (ratMul_zero_left ratZero)

private theorem radialEnergy_zero_to_delta_zero
    (delta : RatNum) (S : List RadialWindowEntry) (hne : S ≠ []) :
    RatEq (radialEnergy delta S) ratZero -> RatEq delta ratZero := by
  intro hE
  unfold radialEnergy at hE
  have hSquareZero : RatEq (ratMul delta delta) ratZero :=
    ratMul_pos_cancel_right_zero (windowConst_pos S hne) hE
  exact ratMul_self_eq_zero_to_zero hSquareZero

private theorem radialEnergy_zero_of_delta_zero
    (delta : RatNum) (S : List RadialWindowEntry) :
    RatEq delta ratZero -> RatEq (radialEnergy delta S) ratZero := by
  intro hdelta
  unfold radialEnergy
  have hSquare : RatEq (ratMul delta delta) ratZero :=
    ratMul_self_zero_of_zero hdelta
  exact RatEq_trans _ _ _
    (ratMul_respects hSquare (RatEq_refl (windowConst S)))
    (ratMul_zero_left (windowConst S))

/-- The finite positive radial window detects exactly the fixed half `delta = 0`. -/
theorem radialEnergy_zero_iff_onCritLine
    (delta : RatNum) (S : List RadialWindowEntry) (hne : S ≠ []) :
    RatEq (radialEnergy delta S) ratZero ↔ RatEq delta ratZero := by
  constructor
  · exact radialEnergy_zero_to_delta_zero delta S hne
  · exact radialEnergy_zero_of_delta_zero delta S

/-- Off the fixed half, the finite radial defect is strictly positive. -/
theorem radialEnergy_pos_of_offCritLine
    (delta : RatNum) (S : List RadialWindowEntry) (hne : S ≠ [])
    (hdelta : RatEq delta ratZero -> False) :
    ratLt ratZero (radialEnergy delta S) := by
  unfold radialEnergy
  exact ratMul_pos_of_pos_pos
    (ratMul_self_pos_of_ne_zero hdelta)
    (windowConst_pos S hne)

end BEDC.Derived.RHRoute.FiniteRadialEnergyCertificate
