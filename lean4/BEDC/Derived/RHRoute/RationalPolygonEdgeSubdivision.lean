import BEDC.Derived.RHRoute.RationalPolygonWindingSubdivision

set_option maxHeartbeats 8000000

namespace BEDC.Derived.RHRoute.RationalPolygonEdgeSubdivision

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RHRoute.RationalPolygonWinding
open BEDC.Derived.RHRoute.RationalPolygonWindingSubdivision

abbrev Rat := BEDC.Derived.RationalUp.RatNum
abbrev RatComplex := BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

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

private theorem ratLeBool_true_to_ratLe {x y : Rat} :
    ratLeBool x y = true -> ratLe x y := by
  intro h
  unfold ratLeBool at h
  unfold ratLe BEDC.Derived.RationalUp.intLe
  exact BEDC.Derived.IntUp.pairLe_of_length_order
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (natLeBool_true_to_le h)

private theorem ratLtBool_true_to_ratLt {x y : Rat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt BEDC.Derived.RationalUp.intLtUp BEDC.Derived.IntUp.intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le h)

private theorem ratLe_to_ratLeBool {x y : Rat} :
    ratLe x y -> ratLeBool x y = true := by
  intro h
  unfold ratLeBool
  unfold ratLe BEDC.Derived.RationalUp.intLe at h
  exact BEDC.Derived.IntUp.natLeBool_true_of_le
    ((BEDC.Derived.IntUp.pairLe_iff_length_order
      (BEDC.Derived.RationalUp.intToPair_carrier _)
      (BEDC.Derived.RationalUp.intToPair_carrier _)).mp h)

private theorem ratLt_to_ratLtBool {x y : Rat} :
    ratLt x y -> ratLtBool x y = true := by
  intro h
  unfold ratLtBool
  unfold ratLt BEDC.Derived.RationalUp.intLtUp BEDC.Derived.IntUp.intLt at h
  exact BEDC.Derived.IntUp.natLeBool_true_of_le (Nat.succ_le_of_lt h)

private theorem ratLeBool_false_of_not_ratLe {x y : Rat} :
    (ratLe x y -> False) -> ratLeBool x y = false := by
  intro notLe
  cases h : ratLeBool x y with
  | false => rfl
  | true => exact False.elim (notLe (ratLeBool_true_to_ratLe h))

private theorem ratLtBool_false_of_not_ratLt {x y : Rat} :
    (ratLt x y -> False) -> ratLtBool x y = false := by
  intro notLt
  cases h : ratLtBool x y with
  | false => rfl
  | true => exact False.elim (notLt (ratLtBool_true_to_ratLt h))

theorem ratLt_of_not_reverse_le {x y : Rat} :
    (ratLe y x -> False) -> ratLt x y := by
  intro notYX
  cases ratLe_total x y with
  | inl xy =>
      exact ratLe_not_le_to_ratLt xy notYX
  | inr yx =>
      exact False.elim (notYX yx)

private theorem ratSub_respects_local {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> RatEq (ratSub x y) (ratSub x' y') := by
  intro xx' yy'
  unfold ratSub
  exact ratAdd_respects xx' (ratNeg_respects yy')

private theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change
    IntEq (IntMul (IntMul x.num intZero) (ratDenInt ratZero))
      (IntMul intZero (ratDenInt (ratMul x ratZero)))
  exact IntEq_trans (intMul_right_congr (intMul_zero_right x.num))
    (IntEq_symm (intMul_zero_left (ratDenInt (ratMul x ratZero))))

private theorem ratMul_neg_right_local (x y : Rat) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem ratMul_sub_left_local (a b c : Rat) :
    RatEq (ratMul a (ratSub b c))
      (ratSub (ratMul a b) (ratMul a c)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Real.RatNumKernel.ratMul_add_left a b (ratNeg c))
    (ratAdd_respects (RatEq_refl (ratMul a b))
      (ratMul_neg_right_local a c))

private theorem ratMul_sub_right_local (a b c : Rat) :
    RatEq (ratMul (ratSub a b) c)
      (ratSub (ratMul a c) (ratMul b c)) := by
  exact RatEq_trans _ _ _
    (ratMul_comm (ratSub a b) c)
    (RatEq_trans _ _ _
      (ratMul_sub_left_local c a b)
      (ratSub_respects_local (ratMul_comm c a) (ratMul_comm c b)))

private theorem ratSub_mul_left_factor_one_sub_local (t x : Rat) :
    RatEq (ratSub x (ratMul t x))
      (ratMul (ratSub ratOne t) x) := by
  exact RatEq_trans _ _ _
    (ratSub_respects_local (RatEq_symm (ratOne_mul_left x))
      (RatEq_refl (ratMul t x)))
    (RatEq_symm (ratMul_sub_right_local ratOne t x))

private theorem ratAdd_sub_swap_local (a x y : Rat) :
    RatEq (ratAdd a (ratSub x y)) (ratAdd (ratSub a y) x) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl a) (ratAdd_comm x (ratNeg y)))
    (RatEq_symm
      (BEDC.Derived.LocatedReal.ratAdd_assoc_local a (ratNeg y) x))

private theorem lerp_im_convex_eq (a b : RatComplex) (t : Rat) :
    RatEq (lerpPoint a b t).im
      (ratAdd (ratMul (ratSub ratOne t) a.im) (ratMul t b.im)) := by
  unfold lerpPoint
  have distribute :
      RatEq (ratMul t (ratSub b.im a.im))
        (ratSub (ratMul t b.im) (ratMul t a.im)) :=
    ratMul_sub_left_local t b.im a.im
  have moveSub :
      RatEq
        (ratAdd a.im (ratSub (ratMul t b.im) (ratMul t a.im)))
        (ratAdd (ratSub a.im (ratMul t a.im)) (ratMul t b.im)) :=
    ratAdd_sub_swap_local a.im (ratMul t b.im) (ratMul t a.im)
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl a.im) distribute)
    (RatEq_trans _ _ _ moveSub
      (ratAdd_respects (ratSub_mul_left_factor_one_sub_local t a.im)
        (RatEq_refl (ratMul t b.im))))

private theorem ratMul_nonpos_of_nonneg_nonpos {x y : Rat} :
    ratLe ratZero x -> ratLe y ratZero -> ratLe (ratMul x y) ratZero := by
  intro xNonneg yNonpos
  have raw : ratLe (ratMul x y) (ratMul x ratZero) :=
    ratMul_le_mul_left yNonpos xNonneg
  exact ratLe_respects (RatEq_refl _) (ratMul_zero_right_local x) raw

private theorem ratAdd_nonpos_of_nonpos {x y : Rat} :
    ratLe x ratZero -> ratLe y ratZero -> ratLe (ratAdd x y) ratZero := by
  intro hx hy
  have raw :
      ratLe (ratAdd x y) (ratAdd ratZero ratZero) :=
    BEDC.Derived.LocatedReal.ratLe_add_mono hx hy
  exact ratLe_respects (RatEq_refl _) (ratZero_add_left ratZero) raw

private theorem ratLt_respects_local {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> ratLt x y -> ratLt x' y' := by
  intro xx' yy' h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_respects xx' yy' (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_respects (RatEq_symm yy') (RatEq_symm xx') reverse)

private theorem ratAdd_right_neg_cancel_local (x y : Rat) :
    RatEq (ratAdd (ratAdd x y) (ratNeg y)) x := by
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x y (ratNeg y))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x)
        (BEDC.Derived.LocatedReal.ratAdd_neg_local y))
      (ratAdd_zero_right x))

private theorem ratLe_add_right_cancel_local {x x' y : Rat} :
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

private theorem ratLt_add_right_mono_local {x x' y : Rat} :
    ratLt x x' -> ratLt (ratAdd x y) (ratAdd x' y) := by
  intro h
  apply ratLe_not_le_to_ratLt
  · exact BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := x) (x' := x') (y := y) (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h (ratLe_add_right_cancel_local reverse)

private theorem ratAdd_pos_of_pos_nonneg {x y : Rat} :
    ratLt ratZero x -> ratLe ratZero y -> ratLt ratZero (ratAdd x y) := by
  intro xPos yNonneg
  have raw : ratLt (ratAdd ratZero y) (ratAdd x y) :=
    ratLt_add_right_mono_local (x := ratZero) (x' := x) (y := y) xPos
  exact ratLe_lt_trans yNonneg
    (ratLt_respects_local (ratZero_add_left y) (RatEq_refl _) raw)

private theorem ratMul_pos_of_pos_pos {x y : Rat} :
    ratLt ratZero x -> ratLt ratZero y -> ratLt ratZero (ratMul x y) := by
  intro xPos yPos
  have raw : ratLt (ratMul x ratZero) (ratMul x y) :=
    ratMul_lt_mul_left yPos xPos
  exact ratLt_respects_local (ratMul_zero_right_local x) (RatEq_refl _) raw

theorem lerp_im_nonpositive_of_endpoints_nonpositive
    (a b : RatComplex) (t : Rat)
    (ht0 : ratLt ratZero t) (ht1 : ratLt t ratOne)
    (aNonpos : ratLe a.im ratZero) (bNonpos : ratLe b.im ratZero) :
    ratLe (lerpPoint a b t).im ratZero := by
  have oneMinusPos : ratLt ratZero (ratSub ratOne t) :=
    sub_pos_of_lt ht1
  have leftNonpos :
      ratLe (ratMul (ratSub ratOne t) a.im) ratZero :=
    ratMul_nonpos_of_nonneg_nonpos
      (ratLt_to_ratLe oneMinusPos) aNonpos
  have rightNonpos : ratLe (ratMul t b.im) ratZero :=
    ratMul_nonpos_of_nonneg_nonpos (ratLt_to_ratLe ht0) bNonpos
  have sumNonpos :
      ratLe
        (ratAdd (ratMul (ratSub ratOne t) a.im) (ratMul t b.im))
        ratZero :=
    ratAdd_nonpos_of_nonpos leftNonpos rightNonpos
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
    (lerp_im_convex_eq a b t) sumNonpos

theorem lerp_im_positive_of_endpoints_positive
    (a b : RatComplex) (t : Rat)
    (ht0 : ratLt ratZero t) (ht1 : ratLt t ratOne)
    (aPos : ratLt ratZero a.im) (bPos : ratLt ratZero b.im) :
    ratLt ratZero (lerpPoint a b t).im := by
  have oneMinusPos : ratLt ratZero (ratSub ratOne t) :=
    sub_pos_of_lt ht1
  have leftPos :
      ratLt ratZero (ratMul (ratSub ratOne t) a.im) :=
    ratMul_pos_of_pos_pos oneMinusPos aPos
  have rightNonneg : ratLe ratZero (ratMul t b.im) :=
    BEDC.Real.RatNumKernel.ratMul_nonneg
      (ratLt_to_ratLe ht0) (ratLt_to_ratLe bPos)
  have sumPos :
      ratLt ratZero
        (ratAdd (ratMul (ratSub ratOne t) a.im) (ratMul t b.im)) :=
    ratAdd_pos_of_pos_nonneg leftPos rightNonneg
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
    sumPos (RatEq_symm (lerp_im_convex_eq a b t))

private theorem positive_not_nonpositive {q : Rat} :
    ratLt ratZero q -> ratLe q ratZero -> False := by
  intro pos nonpos
  exact ratLt_not_ratLe_reverse pos nonpos

private theorem nonpositive_not_positive {q : Rat} :
    ratLe q ratZero -> ratLt ratZero q -> False := by
  intro nonpos pos
  exact ratLt_not_ratLe_reverse pos nonpos

private theorem nonnegative_not_negative {q : Rat} :
    ratLe ratZero q -> ratLt q ratZero -> False := by
  intro nonneg neg
  exact ratLt_not_ratLe_reverse neg nonneg

theorem upwardPositiveRayCrossingBool_true_of_conditions
    {source target : RatComplex}
    (sourceNonpos : ratLe source.im ratZero)
    (targetPos : ratLt ratZero target.im)
    (numPos : ratLt ratZero (rayIntersectionNumerator source target)) :
    upwardPositiveRayCrossingBool source target = true := by
  unfold upwardPositiveRayCrossingBool ratNonPositiveBool ratStrictPositiveBool
  rw [ratLe_to_ratLeBool sourceNonpos]
  rw [ratLt_to_ratLtBool targetPos]
  rw [ratLt_to_ratLtBool numPos]
  rfl

theorem downwardPositiveRayCrossingBool_true_of_conditions
    {source target : RatComplex}
    (targetNonpos : ratLe target.im ratZero)
    (sourcePos : ratLt ratZero source.im)
    (numNeg : ratLt (rayIntersectionNumerator source target) ratZero) :
    downwardPositiveRayCrossingBool source target = true := by
  unfold downwardPositiveRayCrossingBool ratNonPositiveBool
    ratStrictPositiveBool ratStrictNegativeBool
  rw [ratLe_to_ratLeBool targetNonpos]
  rw [ratLt_to_ratLtBool sourcePos]
  rw [ratLt_to_ratLtBool numNeg]
  rfl

theorem upwardPositiveRayCrossingBool_false_of_source_positive
    {source target : RatComplex}
    (sourcePos : ratLt ratZero source.im) :
    upwardPositiveRayCrossingBool source target = false := by
  unfold upwardPositiveRayCrossingBool ratNonPositiveBool
  rw [ratLeBool_false_of_not_ratLe
    (positive_not_nonpositive sourcePos)]
  rfl

theorem upwardPositiveRayCrossingBool_false_of_target_nonpositive
    {source target : RatComplex}
    (targetNonpos : ratLe target.im ratZero) :
    upwardPositiveRayCrossingBool source target = false := by
  unfold upwardPositiveRayCrossingBool ratNonPositiveBool ratStrictPositiveBool
  cases ratLeBool source.im ratZero with
  | false =>
      rfl
  | true =>
      rw [ratLtBool_false_of_not_ratLt
        (nonpositive_not_positive targetNonpos)]
      rfl

theorem upwardPositiveRayCrossingBool_false_of_num_nonpositive
    {source target : RatComplex}
    (numNonpos : ratLe (rayIntersectionNumerator source target) ratZero) :
    upwardPositiveRayCrossingBool source target = false := by
  unfold upwardPositiveRayCrossingBool ratNonPositiveBool ratStrictPositiveBool
  cases ratLeBool source.im ratZero with
  | false =>
      rfl
  | true =>
      cases ratLtBool ratZero target.im with
      | false =>
          rfl
      | true =>
          rw [ratLtBool_false_of_not_ratLt
            (nonpositive_not_positive numNonpos)]
          rfl

theorem downwardPositiveRayCrossingBool_false_of_target_positive
    {source target : RatComplex}
    (targetPos : ratLt ratZero target.im) :
    downwardPositiveRayCrossingBool source target = false := by
  unfold downwardPositiveRayCrossingBool ratNonPositiveBool
  rw [ratLeBool_false_of_not_ratLe
    (positive_not_nonpositive targetPos)]
  rfl

theorem downwardPositiveRayCrossingBool_false_of_source_nonpositive
    {source target : RatComplex}
    (sourceNonpos : ratLe source.im ratZero) :
    downwardPositiveRayCrossingBool source target = false := by
  unfold downwardPositiveRayCrossingBool ratNonPositiveBool ratStrictPositiveBool
  cases ratLeBool target.im ratZero with
  | false =>
      rfl
  | true =>
      rw [ratLtBool_false_of_not_ratLt
        (nonpositive_not_positive sourceNonpos)]
      rfl

theorem downwardPositiveRayCrossingBool_false_of_num_nonnegative
    {source target : RatComplex}
    (numNonneg : ratLe ratZero (rayIntersectionNumerator source target)) :
    downwardPositiveRayCrossingBool source target = false := by
  unfold downwardPositiveRayCrossingBool ratNonPositiveBool
    ratStrictPositiveBool ratStrictNegativeBool
  cases ratLeBool target.im ratZero with
  | false =>
      rfl
  | true =>
      cases ratLtBool ratZero source.im with
      | false =>
          rfl
      | true =>
          rw [ratLtBool_false_of_not_ratLt
            (nonnegative_not_negative numNonneg)]
          rfl

private theorem edgeCrossing_zero_of_crossing_bools_false
    {source target : RatComplex}
    (upFalse : upwardPositiveRayCrossingBool source target = false)
    (downFalse : downwardPositiveRayCrossingBool source target = false) :
    edgeCrossing { source := source, target := target } = 0 := by
  unfold edgeCrossing
  rw [upFalse]
  rw [downFalse]
  rfl

private theorem edgeCrossing_one_of_up_conditions
    {source target : RatComplex}
    (sourceNonpos : ratLe source.im ratZero)
    (targetPos : ratLt ratZero target.im)
    (numPos : ratLt ratZero (rayIntersectionNumerator source target)) :
    edgeCrossing { source := source, target := target } = 1 := by
  unfold edgeCrossing
  rw [upwardPositiveRayCrossingBool_true_of_conditions
    sourceNonpos targetPos numPos]
  rfl

private theorem edgeCrossing_neg_one_of_down_conditions
    {source target : RatComplex}
    (targetNonpos : ratLe target.im ratZero)
    (sourcePos : ratLt ratZero source.im)
    (numNeg : ratLt (rayIntersectionNumerator source target) ratZero) :
    edgeCrossing { source := source, target := target } = -1 := by
  unfold edgeCrossing
  rw [upwardPositiveRayCrossingBool_false_of_source_positive sourcePos]
  rw [downwardPositiveRayCrossingBool_true_of_conditions
    targetNonpos sourcePos numNeg]
  rfl

private theorem edgeCrossing_zero_of_both_nonpositive
    {source target : RatComplex}
    (sourceNonpos : ratLe source.im ratZero)
    (targetNonpos : ratLe target.im ratZero) :
    edgeCrossing { source := source, target := target } = 0 :=
  edgeCrossing_zero_of_crossing_bools_false
    (upwardPositiveRayCrossingBool_false_of_target_nonpositive targetNonpos)
    (downwardPositiveRayCrossingBool_false_of_source_nonpositive sourceNonpos)

private theorem edgeCrossing_zero_of_both_positive
    {source target : RatComplex}
    (sourcePos : ratLt ratZero source.im)
    (targetPos : ratLt ratZero target.im) :
    edgeCrossing { source := source, target := target } = 0 :=
  edgeCrossing_zero_of_upperHalfplane
    (edge := { source := source, target := target }) sourcePos targetPos

private theorem edgeCrossing_zero_of_source_nonpositive_num_nonpositive
    {source target : RatComplex}
    (sourceNonpos : ratLe source.im ratZero)
    (numNonpos : ratLe (rayIntersectionNumerator source target) ratZero) :
    edgeCrossing { source := source, target := target } = 0 :=
  edgeCrossing_zero_of_crossing_bools_false
    (upwardPositiveRayCrossingBool_false_of_num_nonpositive numNonpos)
    (downwardPositiveRayCrossingBool_false_of_source_nonpositive sourceNonpos)

private theorem edgeCrossing_zero_of_target_positive_num_nonpositive
    {source target : RatComplex}
    (targetPos : ratLt ratZero target.im)
    (numNonpos : ratLe (rayIntersectionNumerator source target) ratZero) :
    edgeCrossing { source := source, target := target } = 0 :=
  edgeCrossing_zero_of_crossing_bools_false
    (upwardPositiveRayCrossingBool_false_of_num_nonpositive numNonpos)
    (downwardPositiveRayCrossingBool_false_of_target_positive targetPos)

private theorem edgeCrossing_zero_of_source_positive_num_nonnegative
    {source target : RatComplex}
    (sourcePos : ratLt ratZero source.im)
    (numNonneg : ratLe ratZero (rayIntersectionNumerator source target)) :
    edgeCrossing { source := source, target := target } = 0 :=
  edgeCrossing_zero_of_crossing_bools_false
    (upwardPositiveRayCrossingBool_false_of_source_positive sourcePos)
    (downwardPositiveRayCrossingBool_false_of_num_nonnegative numNonneg)

private theorem edgeCrossing_zero_of_target_nonpositive_num_nonnegative
    {source target : RatComplex}
    (targetNonpos : ratLe target.im ratZero)
    (numNonneg : ratLe ratZero (rayIntersectionNumerator source target)) :
    edgeCrossing { source := source, target := target } = 0 :=
  edgeCrossing_zero_of_crossing_bools_false
    (upwardPositiveRayCrossingBool_false_of_target_nonpositive targetNonpos)
    (downwardPositiveRayCrossingBool_false_of_num_nonnegative numNonneg)

theorem rayNumerator_lerp_source_pos
    {a b : RatComplex} {t : Rat}
    (ht : ratLt ratZero t)
    (numPos : ratLt ratZero (rayIntersectionNumerator a b)) :
    ratLt ratZero (rayIntersectionNumerator a (lerpPoint a b t)) := by
  have productPos :
      ratLt ratZero (ratMul t (rayIntersectionNumerator a b)) :=
    ratMul_pos_of_pos_pos ht numPos
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right productPos
    (RatEq_symm (rayIntersectionNumerator_lerpPoint_source a b t))

theorem rayNumerator_lerp_source_neg
    {a b : RatComplex} {t : Rat}
    (ht : ratLt ratZero t)
    (numNeg : ratLt (rayIntersectionNumerator a b) ratZero) :
    ratLt (rayIntersectionNumerator a (lerpPoint a b t)) ratZero := by
  have productNeg :
      ratLt (ratMul t (rayIntersectionNumerator a b)) ratZero := by
    have raw :
        ratLt (ratMul t (rayIntersectionNumerator a b))
          (ratMul t ratZero) :=
      ratMul_lt_mul_left numNeg ht
    exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right raw
      (ratMul_zero_right_local t)
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_left
    (rayIntersectionNumerator_lerpPoint_source a b t) productNeg

theorem rayNumerator_lerp_source_nonpos
    {a b : RatComplex} {t : Rat}
    (ht : ratLt ratZero t)
    (numNonpos : ratLe (rayIntersectionNumerator a b) ratZero) :
    ratLe (rayIntersectionNumerator a (lerpPoint a b t)) ratZero := by
  have productNonpos :
      ratLe (ratMul t (rayIntersectionNumerator a b)) ratZero :=
    ratMul_nonpos_of_nonneg_nonpos (ratLt_to_ratLe ht) numNonpos
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
    (rayIntersectionNumerator_lerpPoint_source a b t) productNonpos

theorem rayNumerator_lerp_source_nonneg
    {a b : RatComplex} {t : Rat}
    (ht : ratLt ratZero t)
    (numNonneg : ratLe ratZero (rayIntersectionNumerator a b)) :
    ratLe ratZero (rayIntersectionNumerator a (lerpPoint a b t)) := by
  have productNonneg :
      ratLe ratZero (ratMul t (rayIntersectionNumerator a b)) :=
    BEDC.Real.RatNumKernel.ratMul_nonneg
      (ratLt_to_ratLe ht) numNonneg
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
    productNonneg (RatEq_symm (rayIntersectionNumerator_lerpPoint_source a b t))

theorem rayNumerator_lerp_target_pos
    {a b : RatComplex} {t : Rat}
    (ht1 : ratLt t ratOne)
    (numPos : ratLt ratZero (rayIntersectionNumerator a b)) :
    ratLt ratZero (rayIntersectionNumerator (lerpPoint a b t) b) := by
  have factorPos : ratLt ratZero (ratSub ratOne t) :=
    sub_pos_of_lt ht1
  have productPos :
      ratLt ratZero
        (ratMul (ratSub ratOne t) (rayIntersectionNumerator a b)) :=
    ratMul_pos_of_pos_pos factorPos numPos
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right productPos
    (RatEq_symm (rayIntersectionNumerator_lerpPoint_target a b t))

theorem rayNumerator_lerp_target_neg
    {a b : RatComplex} {t : Rat}
    (ht1 : ratLt t ratOne)
    (numNeg : ratLt (rayIntersectionNumerator a b) ratZero) :
    ratLt (rayIntersectionNumerator (lerpPoint a b t) b) ratZero := by
  have factorPos : ratLt ratZero (ratSub ratOne t) :=
    sub_pos_of_lt ht1
  have productNeg :
      ratLt
        (ratMul (ratSub ratOne t) (rayIntersectionNumerator a b))
        ratZero := by
    have raw :
        ratLt
          (ratMul (ratSub ratOne t) (rayIntersectionNumerator a b))
          (ratMul (ratSub ratOne t) ratZero) :=
      ratMul_lt_mul_left numNeg factorPos
    exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right raw
      (ratMul_zero_right_local (ratSub ratOne t))
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_left
    (rayIntersectionNumerator_lerpPoint_target a b t) productNeg

theorem rayNumerator_lerp_target_nonpos
    {a b : RatComplex} {t : Rat}
    (ht1 : ratLt t ratOne)
    (numNonpos : ratLe (rayIntersectionNumerator a b) ratZero) :
    ratLe (rayIntersectionNumerator (lerpPoint a b t) b) ratZero := by
  have factorPos : ratLt ratZero (ratSub ratOne t) :=
    sub_pos_of_lt ht1
  have productNonpos :
      ratLe
        (ratMul (ratSub ratOne t) (rayIntersectionNumerator a b))
        ratZero :=
    ratMul_nonpos_of_nonneg_nonpos
      (ratLt_to_ratLe factorPos) numNonpos
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
    (rayIntersectionNumerator_lerpPoint_target a b t) productNonpos

theorem rayNumerator_lerp_target_nonneg
    {a b : RatComplex} {t : Rat}
    (ht1 : ratLt t ratOne)
    (numNonneg : ratLe ratZero (rayIntersectionNumerator a b)) :
    ratLe ratZero (rayIntersectionNumerator (lerpPoint a b t) b) := by
  have factorPos : ratLt ratZero (ratSub ratOne t) :=
    sub_pos_of_lt ht1
  have productNonneg :
      ratLe ratZero
        (ratMul (ratSub ratOne t) (rayIntersectionNumerator a b)) :=
    BEDC.Real.RatNumKernel.ratMul_nonneg
      (ratLt_to_ratLe factorPos) numNonneg
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
    productNonneg (RatEq_symm (rayIntersectionNumerator_lerpPoint_target a b t))

theorem edgeCrossing_collinear_split
    (a b : RatComplex) (t : Rat)
    (ht0 : ratLt ratZero t) (ht1 : ratLt t ratOne) :
    edgeCrossing { source := a, target := lerpPoint a b t } +
      edgeCrossing { source := lerpPoint a b t, target := b } =
        edgeCrossing { source := a, target := b } := by
  let c := lerpPoint a b t
  change edgeCrossing { source := a, target := c } +
      edgeCrossing { source := c, target := b } =
        edgeCrossing { source := a, target := b }
  cases ratLe_decidable a.im ratZero with
  | inl aNonpos =>
      cases ratLe_decidable b.im ratZero with
      | inl bNonpos =>
          have cNonpos : ratLe c.im ratZero := by
            unfold c
            exact lerp_im_nonpositive_of_endpoints_nonpositive
              a b t ht0 ht1 aNonpos bNonpos
          have leftA := edgeCrossing_zero_of_both_nonpositive
            (source := a) (target := c) aNonpos cNonpos
          have leftB := edgeCrossing_zero_of_both_nonpositive
            (source := c) (target := b) cNonpos bNonpos
          have whole := edgeCrossing_zero_of_both_nonpositive
            (source := a) (target := b) aNonpos bNonpos
          rw [leftA, leftB, whole]
          rfl
      | inr bNotNonpos =>
          have bPos : ratLt ratZero b.im :=
            ratLt_of_not_reverse_le bNotNonpos
          cases ratLe_decidable (rayIntersectionNumerator a b) ratZero with
          | inl numNonpos =>
              have numACNonpos :
                  ratLe (rayIntersectionNumerator a c) ratZero := by
                unfold c
                exact rayNumerator_lerp_source_nonpos ht0 numNonpos
              have numCBNonpos :
                  ratLe (rayIntersectionNumerator c b) ratZero := by
                unfold c
                exact rayNumerator_lerp_target_nonpos ht1 numNonpos
              have leftA :=
                edgeCrossing_zero_of_source_nonpositive_num_nonpositive
                  (source := a) (target := c) aNonpos numACNonpos
              have leftB :=
                edgeCrossing_zero_of_target_positive_num_nonpositive
                  (source := c) (target := b) bPos numCBNonpos
              have whole :=
                edgeCrossing_zero_of_source_nonpositive_num_nonpositive
                  (source := a) (target := b) aNonpos numNonpos
              rw [leftA, leftB, whole]
              rfl
          | inr numNotNonpos =>
              have numPos : ratLt ratZero (rayIntersectionNumerator a b) :=
                ratLt_of_not_reverse_le numNotNonpos
              have whole :=
                edgeCrossing_one_of_up_conditions
                  (source := a) (target := b) aNonpos bPos numPos
              have numACPos :
                  ratLt ratZero (rayIntersectionNumerator a c) := by
                unfold c
                exact rayNumerator_lerp_source_pos ht0 numPos
              have numCBPos :
                  ratLt ratZero (rayIntersectionNumerator c b) := by
                unfold c
                exact rayNumerator_lerp_target_pos ht1 numPos
              cases ratLe_decidable c.im ratZero with
              | inl cNonpos =>
                  have leftA := edgeCrossing_zero_of_both_nonpositive
                    (source := a) (target := c) aNonpos cNonpos
                  have leftB := edgeCrossing_one_of_up_conditions
                    (source := c) (target := b) cNonpos bPos numCBPos
                  rw [leftA, leftB, whole]
                  rfl
              | inr cNotNonpos =>
                  have cPos : ratLt ratZero c.im :=
                    ratLt_of_not_reverse_le cNotNonpos
                  have leftA := edgeCrossing_one_of_up_conditions
                    (source := a) (target := c) aNonpos cPos numACPos
                  have leftB := edgeCrossing_zero_of_both_positive
                    (source := c) (target := b) cPos bPos
                  rw [leftA, leftB, whole]
                  rfl
  | inr aNotNonpos =>
      have aPos : ratLt ratZero a.im :=
        ratLt_of_not_reverse_le aNotNonpos
      cases ratLe_decidable b.im ratZero with
      | inl bNonpos =>
          cases ratLe_decidable ratZero (rayIntersectionNumerator a b) with
          | inl numNonneg =>
              have numACNonneg :
                  ratLe ratZero (rayIntersectionNumerator a c) := by
                unfold c
                exact rayNumerator_lerp_source_nonneg ht0 numNonneg
              have numCBNonneg :
                  ratLe ratZero (rayIntersectionNumerator c b) := by
                unfold c
                exact rayNumerator_lerp_target_nonneg ht1 numNonneg
              have leftA :=
                edgeCrossing_zero_of_source_positive_num_nonnegative
                  (source := a) (target := c) aPos numACNonneg
              have leftB :=
                edgeCrossing_zero_of_target_nonpositive_num_nonnegative
                  (source := c) (target := b) bNonpos numCBNonneg
              have whole :=
                edgeCrossing_zero_of_source_positive_num_nonnegative
                  (source := a) (target := b) aPos numNonneg
              rw [leftA, leftB, whole]
              rfl
          | inr numNotNonneg =>
              have numNeg : ratLt (rayIntersectionNumerator a b) ratZero :=
                ratLt_of_not_reverse_le numNotNonneg
              have whole := edgeCrossing_neg_one_of_down_conditions
                (source := a) (target := b) bNonpos aPos numNeg
              have numACNeg :
                  ratLt (rayIntersectionNumerator a c) ratZero := by
                unfold c
                exact rayNumerator_lerp_source_neg ht0 numNeg
              have numCBNeg :
                  ratLt (rayIntersectionNumerator c b) ratZero := by
                unfold c
                exact rayNumerator_lerp_target_neg ht1 numNeg
              cases ratLe_decidable c.im ratZero with
              | inl cNonpos =>
                  have leftA := edgeCrossing_neg_one_of_down_conditions
                    (source := a) (target := c) cNonpos aPos numACNeg
                  have leftB := edgeCrossing_zero_of_both_nonpositive
                    (source := c) (target := b) cNonpos bNonpos
                  rw [leftA, leftB, whole]
                  rfl
              | inr cNotNonpos =>
                  have cPos : ratLt ratZero c.im :=
                    ratLt_of_not_reverse_le cNotNonpos
                  have leftA := edgeCrossing_zero_of_both_positive
                    (source := a) (target := c) aPos cPos
                  have leftB := edgeCrossing_neg_one_of_down_conditions
                    (source := c) (target := b) bNonpos cPos numCBNeg
                  rw [leftA, leftB, whole]
                  rfl
      | inr bNotNonpos =>
          have bPos : ratLt ratZero b.im :=
            ratLt_of_not_reverse_le bNotNonpos
          have cPos : ratLt ratZero c.im := by
            unfold c
            exact lerp_im_positive_of_endpoints_positive
              a b t ht0 ht1 aPos bPos
          have leftA := edgeCrossing_zero_of_both_positive
            (source := a) (target := c) aPos cPos
          have leftB := edgeCrossing_zero_of_both_positive
            (source := c) (target := b) cPos bPos
          have whole := edgeCrossing_zero_of_both_positive
            (source := a) (target := b) aPos bPos
          rw [leftA, leftB, whole]
          rfl

end BEDC.Derived.RHRoute.RationalPolygonEdgeSubdivision
