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

private abbrev ratRing : RelCommRing Rat RatEq :=
  ratRelCommRing

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

private theorem natLeBool_true_to_le_local {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      cases b with
      | zero =>
          intro h
          cases h
      | succ b =>
          intro h
          exact Nat.succ_le_succ (ih h)

private theorem ratLeBool_true_to_ratLe_local {x y : Rat} :
    ratLeBool x y = true -> ratLe x y := by
  intro h
  unfold ratLeBool at h
  unfold ratLe BEDC.Derived.RationalUp.intLe
  exact BEDC.Derived.IntUp.pairLe_of_length_order
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (natLeBool_true_to_le_local h)

private theorem ratLe_to_ratLeBool_local {x y : Rat} :
    ratLe x y -> ratLeBool x y = true := by
  intro h
  unfold ratLeBool
  unfold ratLe BEDC.Derived.RationalUp.intLe at h
  exact BEDC.Derived.IntUp.natLeBool_true_of_le
    ((BEDC.Derived.IntUp.pairLe_iff_length_order
      (BEDC.Derived.RationalUp.intToPair_carrier _)
      (BEDC.Derived.RationalUp.intToPair_carrier _)).mp h)

def ratMin (x y : Rat) : Rat :=
  if ratLeBool x y then x else y

def ratMax (x y : Rat) : Rat :=
  if ratLeBool x y then y else x

theorem ratMin_le_left (x y : Rat) :
    ratLe (ratMin x y) x := by
  unfold ratMin
  cases h : ratLeBool x y with
  | true =>
      exact ratLe_refl x
  | false =>
      cases ratLe_total x y with
      | inl xy =>
          rw [ratLe_to_ratLeBool_local xy] at h
          cases h
      | inr yx =>
          exact yx

theorem ratMin_le_right (x y : Rat) :
    ratLe (ratMin x y) y := by
  unfold ratMin
  cases h : ratLeBool x y with
  | true =>
      exact ratLeBool_true_to_ratLe_local h
  | false =>
      exact ratLe_refl y

theorem ratMax_ge_left (x y : Rat) :
    ratLe x (ratMax x y) := by
  unfold ratMax
  cases h : ratLeBool x y with
  | true =>
      exact ratLeBool_true_to_ratLe_local h
  | false =>
      exact ratLe_refl x

theorem ratMax_ge_right (x y : Rat) :
    ratLe y (ratMax x y) := by
  unfold ratMax
  cases h : ratLeBool x y with
  | true =>
      exact ratLe_refl y
  | false =>
      cases ratLe_total x y with
      | inl xy =>
          rw [ratLe_to_ratLeBool_local xy] at h
          cases h
      | inr yx =>
          exact yx

def min4 (a b c d : Rat) : Rat :=
  ratMin (ratMin a b) (ratMin c d)

def max4 (a b c d : Rat) : Rat :=
  ratMax (ratMax a b) (ratMax c d)

theorem min4_le_first (a b c d : Rat) :
    ratLe (min4 a b c d) a := by
  unfold min4
  exact ratLe_trans
    (ratMin_le_left (ratMin a b) (ratMin c d))
    (ratMin_le_left a b)

theorem min4_le_second (a b c d : Rat) :
    ratLe (min4 a b c d) b := by
  unfold min4
  exact ratLe_trans
    (ratMin_le_left (ratMin a b) (ratMin c d))
    (ratMin_le_right a b)

theorem min4_le_third (a b c d : Rat) :
    ratLe (min4 a b c d) c := by
  unfold min4
  exact ratLe_trans
    (ratMin_le_right (ratMin a b) (ratMin c d))
    (ratMin_le_left c d)

theorem min4_le_fourth (a b c d : Rat) :
    ratLe (min4 a b c d) d := by
  unfold min4
  exact ratLe_trans
    (ratMin_le_right (ratMin a b) (ratMin c d))
    (ratMin_le_right c d)

theorem first_le_max4 (a b c d : Rat) :
    ratLe a (max4 a b c d) := by
  unfold max4
  exact ratLe_trans
    (ratMax_ge_left a b)
    (ratMax_ge_left (ratMax a b) (ratMax c d))

theorem second_le_max4 (a b c d : Rat) :
    ratLe b (max4 a b c d) := by
  unfold max4
  exact ratLe_trans
    (ratMax_ge_right a b)
    (ratMax_ge_left (ratMax a b) (ratMax c d))

theorem third_le_max4 (a b c d : Rat) :
    ratLe c (max4 a b c d) := by
  unfold max4
  exact ratLe_trans
    (ratMax_ge_left c d)
    (ratMax_ge_right (ratMax a b) (ratMax c d))

theorem fourth_le_max4 (a b c d : Rat) :
    ratLe d (max4 a b c d) := by
  unfold max4
  exact ratLe_trans
    (ratMax_ge_right c d)
    (ratMax_ge_right (ratMax a b) (ratMax c d))

private theorem ratLe_neg_anti_local {a b : Rat} :
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
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local a (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (ratAdd_respects
          (BEDC.Derived.LocatedReal.ratAdd_neg_local a)
          (RatEq_refl (ratNeg b)))
        (ratZero_add_left (ratNeg b)))
  have rightEq : RatEq (ratAdd b t) (ratNeg a) := by
    unfold t
    exact RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl b) (ratAdd_comm (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local b (ratNeg b) (ratNeg a)))
        (RatEq_trans _ _ _
          (ratAdd_respects
            (BEDC.Derived.LocatedReal.ratAdd_neg_local b)
            (RatEq_refl (ratNeg a)))
          (ratZero_add_left (ratNeg a))))
  exact ratLe_respects leftEq rightEq shifted

private theorem ratNeg_nonneg_of_nonpos_local {x : Rat} :
    ratLe x ratZero -> ratLe ratZero (ratNeg x) := by
  intro h
  have subNonneg : ratLe ratZero (ratSub ratZero x) :=
    ratSub_nonneg_of_le h
  exact ratLe_respects (RatEq_refl _)
    (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg x) subNonneg

theorem ratMul_le_mul_right_nonpos {a b c : Rat} :
    ratLe a b -> ratLe c ratZero ->
      ratLe (ratMul b c) (ratMul a c) := by
  intro hab hc
  have negNonneg : ratLe ratZero (ratNeg c) :=
    ratNeg_nonneg_of_nonpos_local hc
  have scaled :
      ratLe (ratMul a (ratNeg c)) (ratMul b (ratNeg c)) :=
    ratMul_le_mul_right hab negNonneg
  have negScaled :
      ratLe (ratNeg (ratMul a c)) (ratNeg (ratMul b c)) :=
    ratLe_respects (ratRing.mul_neg a c) (ratRing.mul_neg b c) scaled
  have raw :
      ratLe (ratNeg (ratNeg (ratMul b c)))
        (ratNeg (ratNeg (ratMul a c))) :=
    ratLe_neg_anti_local negScaled
  exact ratLe_respects
    (BEDC.Derived.LocatedReal.ratNeg_neg_local (ratMul b c))
    (BEDC.Derived.LocatedReal.ratNeg_neg_local (ratMul a c))
    raw

theorem ratMul_le_mul_left_nonpos {a b c : Rat} :
    ratLe a b -> ratLe c ratZero ->
      ratLe (ratMul c b) (ratMul c a) := by
  intro hab hc
  exact ratLe_respects
    (ratMul_comm b c)
    (ratMul_comm a c)
    (ratMul_le_mul_right_nonpos hab hc)

private theorem ratAbs_neg_local (x : Rat) :
    RatEq (ratAbs (ratNeg x)) (ratAbs x) := by
  unfold ratAbs
  exact ratMagnitude_neg x

private theorem ratAbs_eq_self_of_nonneg_local {x : Rat} :
    ratLe ratZero x -> RatEq (ratAbs x) x := by
  intro h
  unfold ratAbs
  exact ratMagnitude_eq_self_of_nonneg h

private theorem ratAbs_eq_neg_of_nonpos_local {x : Rat} :
    ratLe x ratZero -> RatEq (ratAbs x) (ratNeg x) := by
  intro h
  exact RatEq_trans _ _ _
    (RatEq_symm (ratAbs_neg_local x))
    (ratAbs_eq_self_of_nonneg_local (ratNeg_nonneg_of_nonpos_local h))

def offdiagAbsBound (lo hi : Rat) : Rat :=
  ratMax (ratAbs lo) (ratAbs hi)

private theorem ratAbs_interval_bound {lo hi x : Rat} :
    ratLe lo x -> ratLe x hi ->
      ratLe (ratAbs x) (offdiagAbsBound lo hi) := by
  intro hlo hhi
  unfold offdiagAbsBound
  cases ratLe_total ratZero x with
  | inl xNonneg =>
      have xLeBound : ratLe x (ratMax (ratAbs lo) (ratAbs hi)) :=
        ratLe_trans hhi
          (ratLe_trans
            (BEDC.Derived.LocatedReal.ratLe_self_abs hi)
            (ratMax_ge_right (ratAbs lo) (ratAbs hi)))
      exact ratAbs_le_of_nonneg_le xNonneg xLeBound
  | inr xNonpos =>
      have negXLeNegLo : ratLe (ratNeg x) (ratNeg lo) :=
        ratLe_neg_anti_local hlo
      have negXLeBound :
          ratLe (ratNeg x) (ratMax (ratAbs lo) (ratAbs hi)) :=
        ratLe_trans negXLeNegLo
          (ratLe_trans
            (BEDC.Derived.LocatedReal.ratLe_neg_abs lo)
            (ratMax_ge_left (ratAbs lo) (ratAbs hi)))
      have absNegXLe :
          ratLe (ratAbs (ratNeg x)) (ratMax (ratAbs lo) (ratAbs hi)) :=
        ratAbs_le_of_nonneg_le
          (ratNeg_nonneg_of_nonpos_local xNonpos)
          negXLeBound
      exact ratLe_respects
        (ratAbs_neg_local x)
        (RatEq_refl _)
        absNegXLe

private theorem ratSquare_le_of_abs_le {x m : Rat} :
    ratLe (ratAbs x) m ->
      ratLe (ratMul x x) (ratMul m m) := by
  intro hxm
  have absNonneg : ratLe ratZero (ratAbs x) := by
    unfold ratAbs
    exact ratMagnitude_nonneg x
  have absSqLe :
      ratLe (ratMul (ratAbs x) (ratAbs x)) (ratMul m m) :=
    BEDC.Derived.RationalOrderArithUp.mul_le_mul_nonneg
      hxm hxm absNonneg absNonneg
  cases ratLe_total ratZero x with
  | inl xNonneg =>
      have sameSq :
          RatEq (ratMul (ratAbs x) (ratAbs x)) (ratMul x x) :=
        ratMul_respects
          (ratAbs_eq_self_of_nonneg_local xNonneg)
          (ratAbs_eq_self_of_nonneg_local xNonneg)
      exact ratLe_respects sameSq (RatEq_refl _) absSqLe
  | inr xNonpos =>
      have absEqNeg : RatEq (ratAbs x) (ratNeg x) :=
        ratAbs_eq_neg_of_nonpos_local xNonpos
      have sameSq :
          RatEq (ratMul (ratAbs x) (ratAbs x)) (ratMul x x) :=
        RatEq_trans _ _ _
          (ratMul_respects absEqNeg absEqNeg)
          (ratRing.neg_neg_mul_neg x x)
      exact ratLe_respects sameSq (RatEq_refl _) absSqLe

theorem psd_2x2_interval
    (lo11 hi11 lo12 hi12 lo22 hi22 : Rat)
    (_hord11 : ratLe lo11 hi11)
    (_hord12 : ratLe lo12 hi12)
    (_hord22 : ratLe lo22 hi22)
    (hlo11Nonneg : ratLe ratZero lo11)
    (hlo22Nonneg : ratLe ratZero lo22)
    (hdetCert :
      ratLe
        (ratMul (offdiagAbsBound lo12 hi12)
          (offdiagAbsBound lo12 hi12))
        (ratMul lo11 lo22))
    (b11 b12 b22 : Rat)
    (hb11lo : ratLe lo11 b11)
    (_hb11hi : ratLe b11 hi11)
    (hb12lo : ratLe lo12 b12)
    (hb12hi : ratLe b12 hi12)
    (hb22lo : ratLe lo22 b22)
    (_hb22hi : ratLe b22 hi22)
    (c1 c2 : Rat) :
    ratLe ratZero
      (ratAdd
        (ratAdd
          (ratMul b11 (ratMul c1 c1))
          (ratMul (ratMul (natRat 2) b12) (ratMul c1 c2)))
        (ratMul b22 (ratMul c2 c2))) := by
  have h11 : ratLe ratZero b11 :=
    ratLe_trans hlo11Nonneg hb11lo
  have h22 : ratLe ratZero b22 :=
    ratLe_trans hlo22Nonneg hb22lo
  have b12AbsBound :
      ratLe (ratAbs b12) (offdiagAbsBound lo12 hi12) :=
    ratAbs_interval_bound hb12lo hb12hi
  have b12SqLeBoundSq :
      ratLe (ratMul b12 b12)
        (ratMul (offdiagAbsBound lo12 hi12)
          (offdiagAbsBound lo12 hi12)) :=
    ratSquare_le_of_abs_le b12AbsBound
  have loProdLeRealized :
      ratLe (ratMul lo11 lo22) (ratMul b11 b22) :=
    BEDC.Derived.RationalOrderArithUp.mul_le_mul_nonneg
      hb11lo hb22lo hlo11Nonneg hlo22Nonneg
  have hdetB :
      ratLe (ratMul b12 b12) (ratMul b11 b22) :=
    ratLe_trans b12SqLeBoundSq (ratLe_trans hdetCert loProdLeRealized)
  exact psd_2x2 b11 b12 b22 h11 h22 hdetB c1 c2

end BEDC.Derived.RHRoute.IntervalMatrixPSD
