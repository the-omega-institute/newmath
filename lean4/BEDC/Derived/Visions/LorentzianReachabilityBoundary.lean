import BEDC.Derived.Visions.TwoDriverMetricNondegeneracy
import BEDC.Derived.RationalSquareOrderUp
import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

/-!
# Lorentzian reachability boundary for observation Gram metrics

The observation-foundational Gram metric used by `TwoDriverMetricNondegeneracy`
has diagonal self-pairings of the form `Σ w * x * x`. With nonnegative
weights, each displayed self-pairing is nonnegative, so the Gram construction is
locked into a Euclidean semidefinite boundary. A Lorentzian timelike diagonal
direction would require a negative self-pairing, hence cannot be obtained by
this Gram route alone.

This is only a schematic algebraic boundary result. The RH-route file
`ThreeAxisOrbitCollapse` contains a reflection sector with `reflectionWeight =
ratMinusOne` and a manually inserted negative orbit-pair contribution, but that
sector is not imported here and is not connected to the emergent Gram metric.
Obtaining Lorentzian signs would require an additional natural `ι`-twisted
non-Gram form. That construction is open and is not asserted in this file.
-/

namespace BEDC.Derived.Visions

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalSquareOrderUp (rat_order_trichotomy)
open BEDC.Real.RatNumKernel

private theorem ratMul_neg_right_local (x y : RatNum) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem ratMul_neg_left_local (x y : RatNum) :
    RatEq (ratMul (ratNeg x) y) (ratNeg (ratMul x y)) := by
  exact RatEq_trans _ _ _
    (ratMul_comm (ratNeg x) y)
    (RatEq_trans _ _ _
      (ratMul_neg_right_local y x)
      (ratNeg_respects (ratMul_comm y x)))

private theorem ratMul_neg_neg_eq_mul_local (x y : RatNum) :
    RatEq (ratMul (ratNeg x) (ratNeg y)) (ratMul x y) := by
  exact RatEq_trans _ _ _
    (ratMul_neg_left_local x (ratNeg y))
    (RatEq_trans _ _ _
      (ratNeg_respects (ratMul_neg_right_local x y))
      (BEDC.Derived.LocatedReal.ratNeg_neg_local (ratMul x y)))

private theorem ratNeg_nonneg_of_nonpos_local {x : RatNum} :
    ratLe x ratZero -> ratLe ratZero (ratNeg x) := by
  intro h
  have subNonneg : ratLe ratZero (ratSub ratZero x) :=
    ratSub_nonneg_of_le h
  exact ratLe_of_RatEq_right subNonneg
    (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg x)

theorem ratMul_self_nonneg (a : RatNum) :
    ratLe ratZero (ratMul a a) := by
  cases rat_order_trichotomy ratZero a with
  | inl hpos =>
      exact ratMul_nonneg (ratLt_to_ratLe hpos) (ratLt_to_ratLe hpos)
  | inr hrest =>
      cases hrest with
      | inl hzero =>
          exact ratMul_nonneg (ratLe_of_RatEq hzero) (ratLe_of_RatEq hzero)
      | inr hneg =>
          have negNonneg : ratLe ratZero (ratNeg a) :=
            ratNeg_nonneg_of_nonpos_local (ratLt_to_ratLe hneg)
          have raw : ratLe ratZero (ratMul (ratNeg a) (ratNeg a)) :=
            ratMul_nonneg negNonneg negNonneg
          exact ratLe_of_RatEq_right raw (ratMul_neg_neg_eq_mul_local a a)

private theorem ratAdd_nonneg_local {x y : RatNum}
    (hx : ratLe ratZero x) (hy : ratLe ratZero y) :
    ratLe ratZero (ratAdd x y) := by
  have raw : ratLe (ratAdd ratZero ratZero) (ratAdd x y) :=
    ratAdd_le_add hx hy
  exact ratLe_of_RatEq_left (ratZero_add_left ratZero) raw

private theorem ratWeightedSquare_nonneg (w x : RatNum)
    (hw : ratLe ratZero w) :
    ratLe ratZero (ratMul (ratMul w x) x) := by
  have productNonneg : ratLe ratZero (ratMul w (ratMul x x)) :=
    ratMul_nonneg hw (ratMul_self_nonneg x)
  exact ratLe_of_RatEq_right productNonneg (RatEq_symm (ratMul_assoc w x x))

theorem observation_gram_diag_nonneg
    (w1 w2 a1 a2 b1 b2 : RatNum)
    (hw1 : ratLe ratZero w1) (hw2 : ratLe ratZero w2) :
    ratLe ratZero (twoDriverGXX w1 w2 a1 a2 b1 b2) ∧
      ratLe ratZero (twoDriverGYY w1 w2 a1 a2 b1 b2) := by
  constructor
  · unfold twoDriverGXX
    exact ratAdd_nonneg_local
      (ratWeightedSquare_nonneg w1 a1 hw1)
      (ratWeightedSquare_nonneg w2 b1 hw2)
  · unfold twoDriverGYY
    exact ratAdd_nonneg_local
      (ratWeightedSquare_nonneg w1 a2 hw1)
      (ratWeightedSquare_nonneg w2 b2 hw2)

theorem lorentzian_diagonal_excluded
    (w1 w2 a1 a2 b1 b2 : RatNum)
    (hw1 : ratLe ratZero w1) (hw2 : ratLe ratZero w2) :
    (ratLt (twoDriverGXX w1 w2 a1 a2 b1 b2) ratZero -> False) ∧
      (ratLt (twoDriverGYY w1 w2 a1 a2 b1 b2) ratZero -> False) := by
  have diag := observation_gram_diag_nonneg w1 w2 a1 a2 b1 b2 hw1 hw2
  constructor
  · intro hlt
    exact ratLt_not_ratLe_reverse hlt diag.left
  · intro hlt
    exact ratLt_not_ratLe_reverse hlt diag.right

end BEDC.Derived.Visions
