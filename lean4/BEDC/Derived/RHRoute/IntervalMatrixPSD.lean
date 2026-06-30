import BEDC.Derived.RHRoute.IntervalMatrixPSD.AlgebraNormalize

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD

open BEDC.Algebra.Rel (RelCommRing)
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp

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

private def ratRing : RelCommRing Rat RatEq where
  zero := ratZero
  one := ratOne
  add := ratAdd
  mul := ratMul
  neg := ratNeg
  refl := RatEq_refl
  symm := RatEq_symm
  trans := by
    intro _ _ _
    exact RatEq_trans _ _ _
  add_congr := by
    intro _ _ _ _ hleft hright
    exact ratAdd_respects hleft hright
  mul_congr := by
    intro _ _ _ _ hleft hright
    exact ratMul_respects hleft hright
  neg_congr := by
    intro _ _ h
    exact ratNeg_respects h
  add_assoc := BEDC.Derived.LocatedReal.ratAdd_assoc_local
  add_comm := ratAdd_comm
  add_zero := ratAdd_zero_right
  zero_add := ratZero_add_left
  add_neg := BEDC.Derived.LocatedReal.ratAdd_neg_local
  neg_add := BEDC.Derived.LocatedReal.ratNeg_add_local
  mul_assoc := ratMul_assoc
  mul_one := ratMul_one_right
  one_mul := ratOne_mul_left
  mul_zero := ratMul_zero_right_local
  zero_mul := ratMul_zero_left_local
  left_distrib := BEDC.Real.RatNumKernel.ratMul_add_left
  right_distrib := BEDC.Real.RatNumKernel.ratMul_add_right
  mul_comm := ratMul_comm

private theorem ratNeg_pos_of_neg {x : Rat} :
    ratLt x ratZero -> ratLt ratZero (ratNeg x) := by
  intro h
  have subPos : ratLt ratZero (ratSub ratZero x) :=
    sub_pos_of_lt h
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
    subPos
    (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg x)

private theorem ratSquare_nonneg (x : Rat) :
    ratLe ratZero (ratMul x x) := by
  cases rat_order_trichotomy ratZero x with
  | inl xPos =>
      exact BEDC.Real.RatNumKernel.ratMul_nonneg
        (ratLt_to_ratLe xPos) (ratLt_to_ratLe xPos)
  | inr rest =>
      cases rest with
      | inl xZero =>
          have squareZero : RatEq (ratMul x x) ratZero := by
            exact RatEq_trans _ _ _
              (ratMul_respects (RatEq_symm xZero) (RatEq_symm xZero))
              (ratMul_zero_left_local ratZero)
          exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
            (ratLe_refl ratZero) (RatEq_symm squareZero)
      | inr xNeg =>
          have negNonneg : ratLe ratZero (ratNeg x) :=
            ratLt_to_ratLe (ratNeg_pos_of_neg xNeg)
          have negSquareNonneg :
              ratLe ratZero (ratMul (ratNeg x) (ratNeg x)) :=
            BEDC.Real.RatNumKernel.ratMul_nonneg negNonneg negNonneg
          have sameSquare :
              RatEq (ratMul (ratNeg x) (ratNeg x)) (ratMul x x) :=
            ratRing.neg_neg_mul_neg x x
          exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
            negSquareNonneg sameSquare

theorem psd_1x1 (b c : Rat)
    (hb : ratLe ratZero b) :
    ratLe ratZero (ratMul b (ratMul c c)) := by
  exact BEDC.Real.RatNumKernel.ratMul_nonneg hb (ratSquare_nonneg c)

private theorem ratAdd_nonneg {x y : Rat} :
    ratLe ratZero x -> ratLe ratZero y -> ratLe ratZero (ratAdd x y) := by
  intro hx hy
  have raw :
      ratLe (ratAdd ratZero ratZero) (ratAdd x y) :=
    BEDC.Real.RatNumKernel.ratAdd_le_add hx hy
  exact ratLe_respects (ratZero_add_left ratZero) (RatEq_refl _) raw

private theorem ratLe_of_mul_pos_left {a x : Rat} :
    ratLt ratZero a -> ratLe ratZero (ratMul a x) -> ratLe ratZero x := by
  intro apos h
  have productRight :
      ratLe (ratMul ratZero a) (ratMul x a) :=
    ratLe_respects
      (RatEq_symm (ratMul_zero_left_local a))
      (ratMul_comm a x)
      h
  exact ratMul_le_cancel_right apos productRight

private theorem ratLt_square_of_pos {x : Rat} :
    ratLt ratZero x -> ratLt ratZero (ratMul x x) := by
  intro xpos
  have raw : ratLt (ratMul ratZero x) (ratMul x x) :=
    ratMul_lt_mul_right xpos xpos
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_left
    (RatEq_symm (ratMul_zero_left_local x))
    raw

private theorem ratLt_square_of_neg {x : Rat} :
    ratLt x ratZero -> ratLt ratZero (ratMul x x) := by
  intro xneg
  have negPos : ratLt ratZero (ratNeg x) :=
    ratNeg_pos_of_neg xneg
  have negSqPos : ratLt ratZero (ratMul (ratNeg x) (ratNeg x)) :=
    ratLt_square_of_pos negPos
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
    negSqPos
    (ratRing.neg_neg_mul_neg x x)

private theorem ratZero_of_square_le_zero {x : Rat} :
    ratLe (ratMul x x) ratZero -> RatEq x ratZero := by
  intro sqLeZero
  cases rat_order_trichotomy ratZero x with
  | inl xpos =>
      exact False.elim
        (ratLt_not_ratLe_reverse (ratLt_square_of_pos xpos) sqLeZero)
  | inr rest =>
      cases rest with
      | inl xzero => exact RatEq_symm xzero
      | inr xneg =>
          exact False.elim
            (ratLt_not_ratLe_reverse (ratLt_square_of_neg xneg) sqLeZero)

private theorem complete_square_nonneg
    {b11 b12 b22 c1 c2 : Rat}
    (hdet : ratLe (ratMul b12 b12) (ratMul b11 b22)) :
    ratLe ratZero
      (ratAdd
        (ratMul
          (ratAdd (ratMul b11 c1) (ratMul b12 c2))
          (ratAdd (ratMul b11 c1) (ratMul b12 c2)))
        (ratMul
          (ratSub (ratMul b11 b22) (ratMul b12 b12))
          (ratMul c2 c2))) := by
  apply ratAdd_nonneg
  · exact ratSquare_nonneg
      (ratAdd (ratMul b11 c1) (ratMul b12 c2))
  · exact BEDC.Real.RatNumKernel.ratMul_nonneg
      (ratSub_nonneg_of_le hdet)
      (ratSquare_nonneg c2)

private theorem psd_2x2_pos_diag_core
    (b11 b12 b22 c1 c2 : Rat)
    (h11pos : ratLt ratZero b11)
    (hdet : ratLe (ratMul b12 b12) (ratMul b11 b22)) :
    ratLe ratZero
      (ratAdd
        (ratAdd
          (ratMul b11 (ratMul c1 c1))
          (ratMul (ratMul (natRat 2) b12) (ratMul c1 c2)))
        (ratMul b22 (ratMul c2 c2))) := by
  let Q :=
    ratAdd
      (ratAdd
        (ratMul b11 (ratMul c1 c1))
        (ratMul (ratMul (natRat 2) b12) (ratMul c1 c2)))
      (ratMul b22 (ratMul c2 c2))
  have bridge := complete_square_identity b11 b12 b22 c1 c2
  have rhsNonneg :
      ratLe ratZero
        (ratAdd
          (ratMul
            (ratAdd (ratMul b11 c1) (ratMul b12 c2))
            (ratAdd (ratMul b11 c1) (ratMul b12 c2)))
          (ratMul
            (ratSub (ratMul b11 b22) (ratMul b12 b12))
            (ratMul c2 c2))) :=
    complete_square_nonneg hdet
  have b11QNonneg :
      ratLe ratZero (ratMul b11 Q) :=
    BEDC.Real.RatNumKernel.ratLe_of_RatEq_right rhsNonneg
      (RatEq_symm bridge)
  exact ratLe_of_mul_pos_left h11pos b11QNonneg

private theorem q_eq_tail_when_b11_b12_zero
    (b11 b12 b22 c1 c2 : Rat)
    (hb11 : RatEq b11 ratZero)
    (hb12 : RatEq b12 ratZero) :
    RatEq
      (ratAdd
        (ratAdd
          (ratMul b11 (ratMul c1 c1))
          (ratMul (ratMul (natRat 2) b12) (ratMul c1 c2)))
        (ratMul b22 (ratMul c2 c2)))
      (ratMul b22 (ratMul c2 c2)) := by
  have twoB12Zero :
      RatEq (ratMul (natRat 2) b12) ratZero := by
    exact RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl (natRat 2)) hb12)
      (ratMul_zero_right_local (natRat 2))
  have firstZero :
      RatEq (ratMul b11 (ratMul c1 c1)) ratZero := by
    exact RatEq_trans _ _ _
      (ratMul_respects hb11 (RatEq_refl (ratMul c1 c1)))
      (ratMul_zero_left_local (ratMul c1 c1))
  have crossZero :
      RatEq (ratMul (ratMul (natRat 2) b12) (ratMul c1 c2)) ratZero := by
    exact RatEq_trans _ _ _
      (ratMul_respects twoB12Zero (RatEq_refl (ratMul c1 c2)))
      (ratMul_zero_left_local (ratMul c1 c2))
  exact RatEq_trans _ _ _
    (ratAdd_respects
      (ratAdd_respects firstZero crossZero)
      (RatEq_refl (ratMul b22 (ratMul c2 c2))))
    (RatEq_trans _ _ _
      (ratAdd_respects (ratZero_add_left ratZero)
        (RatEq_refl (ratMul b22 (ratMul c2 c2))))
      (ratZero_add_left (ratMul b22 (ratMul c2 c2))))

theorem psd_2x2
    (b11 b12 b22 : Rat)
    (h11 : ratLe ratZero b11)
    (h22 : ratLe ratZero b22)
    (hdet : ratLe (ratMul b12 b12) (ratMul b11 b22))
    (c1 c2 : Rat) :
    ratLe ratZero
      (ratAdd
        (ratAdd
          (ratMul b11 (ratMul c1 c1))
          (ratMul (ratMul (natRat 2) b12) (ratMul c1 c2)))
        (ratMul b22 (ratMul c2 c2))) := by
  cases rat_order_trichotomy ratZero b11 with
  | inl h11pos =>
      have core :
          ratLe ratZero
            (ratAdd
              (ratAdd
                (ratMul b11 (ratMul c1 c1))
                (ratMul (ratMul (natRat 2) b12) (ratMul c1 c2)))
              (ratMul b22 (ratMul c2 c2))) :=
        psd_2x2_pos_diag_core b11 b12 b22 c1 c2 h11pos hdet
      exact core
  | inr rest =>
      cases rest with
      | inl h11zero =>
          have b11b22Zero :
              RatEq (ratMul b11 b22) ratZero := by
            exact RatEq_trans _ _ _
              (ratMul_respects (RatEq_symm h11zero) (RatEq_refl b22))
              (ratMul_zero_left_local b22)
          have b12sqLeZero : ratLe (ratMul b12 b12) ratZero :=
            BEDC.Real.RatNumKernel.ratLe_of_RatEq_right hdet b11b22Zero
          have h12zero : RatEq b12 ratZero :=
            ratZero_of_square_le_zero b12sqLeZero
          have tailNonneg :
              ratLe ratZero (ratMul b22 (ratMul c2 c2)) :=
            psd_1x1 b22 c2 h22
          exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right tailNonneg
            (RatEq_symm
              (q_eq_tail_when_b11_b12_zero b11 b12 b22 c1 c2
                (RatEq_symm h11zero) h12zero))
      | inr h11neg =>
          exact False.elim (ratLt_not_ratLe_reverse h11neg h11)

end BEDC.Derived.RHRoute.IntervalMatrixPSD
