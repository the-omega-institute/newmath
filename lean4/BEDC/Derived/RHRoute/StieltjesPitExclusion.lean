import BEDC.Real.RatNumKernel
import BEDC.Real.RatNumLogEnclosure
import BEDC.Derived.LocatedReal.GroundedToleranceKit

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.StieltjesPitExclusion

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure
open BEDC.Derived.LocatedReal

abbrev Rat : Type :=
  RatNum

/--
Finite complex algebra kernel for the Stieltjes pole-location obstruction:
an off-line candidate with `Re(w)` apart from zero cannot place `w^2 - 1`
inside the real-axis pit `(-infty, -1]` allowed by a positive Stieltjes
transform. This is not RH: the analytic assertion that `S_xi` is a positive
Stieltjes transform, and its equivalence with RH, is not formalized or
claimed here. The checked content is only the finite pole-location
incompatibility.
-/
structure RatComplexPit where
  re : RatNum
  im : RatNum

def sqMinus1_im (w : RatComplexPit) : RatNum :=
  ratMul ratTwo (ratMul w.re w.im)

def sqMinus1_re (w : RatComplexPit) : RatNum :=
  ratSub (ratSub (ratMul w.re w.re) (ratMul w.im w.im)) ratOne

private theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change
    IntEq (IntMul (IntMul x.num intZero) (ratDenInt ratZero))
      (IntMul intZero (ratDenInt (ratMul x ratZero)))
  exact IntEq_trans (intMul_right_congr (intMul_zero_right x.num))
    (IntEq_symm (intMul_zero_left (ratDenInt (ratMul x ratZero))))

private theorem ratMul_zero_left_local (x : Rat) :
    RatEq (ratMul ratZero x) ratZero :=
  RatEq_trans _ _ _ (ratMul_comm ratZero x) (ratMul_zero_right_local x)

private theorem ratApart0_not_RatEq_zero {x : Rat} :
    ratApart0 x -> RatEq x ratZero -> False := by
  intro hx hzero
  exact intApart0_not_zero_pair hx (RatEq_zero_num hzero)

private theorem ratMul_eq_zero_right_of_left_apart
    {x y : Rat} (hx : ratApart0 x) :
    RatEq (ratMul x y) ratZero -> RatEq y ratZero := by
  intro hxy
  exact ratMul_right_cancel_apart0 y ratZero x hx
    (RatEq_trans _ _ _
      (RatEq_symm (ratMul_comm x y))
      (RatEq_trans _ _ _ hxy (RatEq_symm (ratMul_zero_left_local x))))

private theorem ratMul_eq_zero_right_of_left_apart_assoc
    {x y z : Rat} (hx : ratApart0 x) (hy : ratApart0 y) :
    RatEq (ratMul x (ratMul y z)) ratZero -> RatEq z ratZero := by
  intro h
  have yzZero : RatEq (ratMul y z) ratZero :=
    ratMul_eq_zero_right_of_left_apart hx h
  exact ratMul_eq_zero_right_of_left_apart hy yzZero

private theorem ratMul_neg_right_local (x y : Rat) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem ratMul_neg_left_local (x y : Rat) :
    RatEq (ratMul (ratNeg x) y) (ratNeg (ratMul x y)) := by
  exact RatEq_trans _ _ _
    (ratMul_comm (ratNeg x) y)
    (RatEq_trans _ _ _
      (ratMul_neg_right_local y x)
      (ratNeg_respects (ratMul_comm y x)))

private theorem ratMul_neg_neg_local (x y : Rat) :
    RatEq (ratMul (ratNeg x) (ratNeg y)) (ratMul x y) := by
  exact RatEq_trans _ _ _
    (ratMul_neg_left_local x (ratNeg y))
    (RatEq_trans _ _ _
      (ratNeg_respects (ratMul_neg_right_local x y))
      (ratNeg_neg_local (ratMul x y)))

private theorem ratSq_nonneg (x : Rat) :
    ratLe ratZero (ratMul x x) := by
  cases rat_order_trichotomy ratZero x with
  | inl xPos =>
      exact ratMul_nonneg (ratLt_to_ratLe xPos) (ratLt_to_ratLe xPos)
  | inr rest =>
      cases rest with
      | inl xZero =>
          have squareZero : RatEq (ratMul x x) ratZero := by
            exact RatEq_trans _ _ _
              (ratMul_respects (RatEq_symm xZero) (RatEq_symm xZero))
              (ratMul_zero_left_local ratZero)
          exact ratLe_of_RatEq_right (ratLe_refl ratZero) (RatEq_symm squareZero)
      | inr xNeg =>
          have negNonneg : ratLe ratZero (ratNeg x) := by
            have subPos : ratLt ratZero (ratSub ratZero x) :=
              sub_pos_of_lt xNeg
            exact ratLt_to_ratLe
              (ratLt_of_RatEq_right subPos (ratZero_sub_eq_neg x))
          have negSquareNonneg :
              ratLe ratZero (ratMul (ratNeg x) (ratNeg x)) :=
            ratMul_nonneg negNonneg negNonneg
          exact ratLe_of_RatEq_right negSquareNonneg
            (ratMul_neg_neg_local x x)

private theorem ratSq_pos_of_apart0 {x : Rat} :
    ratApart0 x -> ratLt ratZero (ratMul x x) := by
  intro hx
  apply ratLe_not_le_to_ratLt
  · exact ratSq_nonneg x
  · intro sqLeZero
    have sqZero : RatEq (ratMul x x) ratZero :=
      ratLe_antisymm sqLeZero (ratSq_nonneg x)
    exact ratApart0_not_RatEq_zero (ratMul_apart0 hx hx) sqZero

private theorem ratSub_add_cancel_right_local (x y : Rat) :
    RatEq (ratAdd (ratSub x y) y) x := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_assoc_local x (ratNeg y) y)
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x) (ratNeg_add_local y))
      (ratAdd_zero_right x))

private theorem ratNeg_zero_local :
    RatEq (ratNeg ratZero) ratZero := by
  exact RatEq_trans _ _ _
    (ratNeg_add_local ratZero)
    (RatEq_symm (ratAdd_zero_right (ratNeg ratZero)))

private theorem ratSub_zero_right_local (x : Rat) :
    RatEq (ratSub x ratZero) x := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl x) ratNeg_zero_local)
    (ratAdd_zero_right x)

private theorem ratSub_one_le_neg_one_to_le_zero {x : Rat} :
    ratLe (ratSub x ratOne) (ratNeg ratOne) -> ratLe x ratZero := by
  intro h
  have shifted :
      ratLe (ratAdd (ratSub x ratOne) ratOne)
        (ratAdd (ratNeg ratOne) ratOne) :=
    ratLe_add_right_mono (x := ratSub x ratOne) (x' := ratNeg ratOne)
      (y := ratOne) h
  exact ratLe_respects
    (ratSub_add_cancel_right_local x ratOne)
    (ratNeg_add_local ratOne)
    shifted

private theorem ratSub_right_respects {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> RatEq (ratSub x y) (ratSub x' y') := by
  intro hx hy
  unfold ratSub
  exact ratAdd_respects hx (ratNeg_respects hy)

private theorem sqMinus1_re_of_im_zero
    (w : RatComplexPit) :
    RatEq w.im ratZero ->
      RatEq (sqMinus1_re w) (ratSub (ratMul w.re w.re) ratOne) := by
  intro him
  unfold sqMinus1_re
  have imSqZero : RatEq (ratMul w.im w.im) ratZero :=
    RatEq_trans _ _ _
      (ratMul_respects him him)
      (ratMul_zero_left_local ratZero)
  exact ratSub_right_respects
    (RatEq_trans _ _ _
      (ratSub_right_respects (RatEq_refl (ratMul w.re w.re)) imSqZero)
      (ratSub_zero_right_local (ratMul w.re w.re)))
    (RatEq_refl ratOne)

private theorem sqMinus1_re_le_neg_one_to_sq_le_zero
    (w : RatComplexPit) :
    RatEq w.im ratZero ->
      ratLe (sqMinus1_re w) (ratNeg ratOne) ->
        ratLe (ratMul w.re w.re) ratZero := by
  intro him hle
  exact ratSub_one_le_neg_one_to_le_zero
    (ratLe_respects
      (sqMinus1_re_of_im_zero w him)
      (RatEq_refl (ratNeg ratOne))
      hle)

theorem offCritical_pit_exclusion
    (w : RatComplexPit) (hre : ratApart0 w.re) :
    ¬ (RatEq (sqMinus1_im w) ratZero ∧
      ratLe (sqMinus1_re w) (ratNeg ratOne)) := by
  intro h
  cases h with
  | intro him0 hle =>
      have imZero : RatEq w.im ratZero := by
        unfold sqMinus1_im at him0
        exact ratMul_eq_zero_right_of_left_apart_assoc ratTwo_apart hre him0
      have sqLeZero : ratLe (ratMul w.re w.re) ratZero :=
        sqMinus1_re_le_neg_one_to_sq_le_zero w imZero hle
      exact ratLt_not_ratLe_reverse (ratSq_pos_of_apart0 hre) sqLeZero

theorem onCritical_pit_allows
    (w : RatComplexPit) (hre : RatEq w.re ratZero) :
    RatEq (sqMinus1_im w) ratZero := by
  unfold sqMinus1_im
  exact RatEq_trans _ _ _
    (ratMul_respects (RatEq_refl ratTwo)
      (ratMul_respects hre (RatEq_refl w.im)))
    (RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl ratTwo) (ratMul_zero_left_local w.im))
      (ratMul_zero_right_local ratTwo))

end BEDC.Derived.RHRoute.StieltjesPitExclusion
