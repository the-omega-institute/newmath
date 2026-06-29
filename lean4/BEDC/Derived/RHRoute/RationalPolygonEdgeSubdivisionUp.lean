import BEDC.Derived.RHRoute.RationalPolygonEdgeSubdivision

set_option maxHeartbeats 8000000

namespace BEDC.Derived.RHRoute.RationalPolygonEdgeSubdivision

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RHRoute.RationalPolygonWinding
open BEDC.Derived.RHRoute.RationalPolygonWindingSubdivision

private theorem edgeCrossingUp_zero_of_crossing_bools_false
    {source target : RatComplex}
    (upFalse : upwardPositiveRayCrossingBool source target = false)
    (downFalse : downwardPositiveRayCrossingBool source target = false) :
    IntEq (edgeCrossingUp { source := source, target := target }) intZero := by
  unfold edgeCrossingUp
  rw [upFalse]
  rw [downFalse]
  exact IntEq_refl intZero

private theorem edgeCrossingUp_one_of_up_conditions
    {source target : RatComplex}
    (sourceNonpos : ratLe source.im ratZero)
    (targetPos : ratLt ratZero target.im)
    (numPos : ratLt ratZero (rayIntersectionNumerator source target)) :
    IntEq (edgeCrossingUp { source := source, target := target }) intOne := by
  unfold edgeCrossingUp
  rw [upwardPositiveRayCrossingBool_true_of_conditions
    sourceNonpos targetPos numPos]
  exact IntEq_refl intOne

private theorem edgeCrossingUp_neg_one_of_down_conditions
    {source target : RatComplex}
    (targetNonpos : ratLe target.im ratZero)
    (sourcePos : ratLt ratZero source.im)
    (numNeg : ratLt (rayIntersectionNumerator source target) ratZero) :
    IntEq (edgeCrossingUp { source := source, target := target })
      (IntNeg intOne) := by
  unfold edgeCrossingUp
  rw [upwardPositiveRayCrossingBool_false_of_source_positive sourcePos]
  rw [downwardPositiveRayCrossingBool_true_of_conditions
    targetNonpos sourcePos numNeg]
  exact IntEq_refl (IntNeg intOne)

private theorem edgeCrossingUp_zero_of_both_nonpositive
    {source target : RatComplex}
    (sourceNonpos : ratLe source.im ratZero)
    (targetNonpos : ratLe target.im ratZero) :
    IntEq (edgeCrossingUp { source := source, target := target }) intZero :=
  edgeCrossingUp_zero_of_crossing_bools_false
    (upwardPositiveRayCrossingBool_false_of_target_nonpositive targetNonpos)
    (downwardPositiveRayCrossingBool_false_of_source_nonpositive sourceNonpos)

private theorem edgeCrossingUp_zero_of_both_positive
    {source target : RatComplex}
    (sourcePos : ratLt ratZero source.im)
    (targetPos : ratLt ratZero target.im) :
    IntEq (edgeCrossingUp { source := source, target := target }) intZero :=
  edgeCrossingUp_zero_of_crossing_bools_false
    (upwardPositiveRayCrossingBool_false_of_source_positive sourcePos)
    (downwardPositiveRayCrossingBool_false_of_target_positive targetPos)

private theorem edgeCrossingUp_zero_of_source_nonpositive_num_nonpositive
    {source target : RatComplex}
    (sourceNonpos : ratLe source.im ratZero)
    (numNonpos : ratLe (rayIntersectionNumerator source target) ratZero) :
    IntEq (edgeCrossingUp { source := source, target := target }) intZero :=
  edgeCrossingUp_zero_of_crossing_bools_false
    (upwardPositiveRayCrossingBool_false_of_num_nonpositive numNonpos)
    (downwardPositiveRayCrossingBool_false_of_source_nonpositive sourceNonpos)

private theorem edgeCrossingUp_zero_of_target_positive_num_nonpositive
    {source target : RatComplex}
    (targetPos : ratLt ratZero target.im)
    (numNonpos : ratLe (rayIntersectionNumerator source target) ratZero) :
    IntEq (edgeCrossingUp { source := source, target := target }) intZero :=
  edgeCrossingUp_zero_of_crossing_bools_false
    (upwardPositiveRayCrossingBool_false_of_num_nonpositive numNonpos)
    (downwardPositiveRayCrossingBool_false_of_target_positive targetPos)

private theorem edgeCrossingUp_zero_of_source_positive_num_nonnegative
    {source target : RatComplex}
    (sourcePos : ratLt ratZero source.im)
    (numNonneg : ratLe ratZero (rayIntersectionNumerator source target)) :
    IntEq (edgeCrossingUp { source := source, target := target }) intZero :=
  edgeCrossingUp_zero_of_crossing_bools_false
    (upwardPositiveRayCrossingBool_false_of_source_positive sourcePos)
    (downwardPositiveRayCrossingBool_false_of_num_nonnegative numNonneg)

private theorem edgeCrossingUp_zero_of_target_nonpositive_num_nonnegative
    {source target : RatComplex}
    (targetNonpos : ratLe target.im ratZero)
    (numNonneg : ratLe ratZero (rayIntersectionNumerator source target)) :
    IntEq (edgeCrossingUp { source := source, target := target }) intZero :=
  edgeCrossingUp_zero_of_crossing_bools_false
    (upwardPositiveRayCrossingBool_false_of_target_nonpositive targetNonpos)
    (downwardPositiveRayCrossingBool_false_of_num_nonnegative numNonneg)

private theorem edgeCrossingUp_sum_from_values
    {x y z xValue yValue zValue : WindingInteger}
    (hx : IntEq x xValue) (hy : IntEq y yValue) (hz : IntEq z zValue)
    (hxy : IntEq (IntAdd xValue yValue) zValue) :
    IntEq (IntAdd x y) z :=
  IntEq_trans (IntAdd_respects hx hy)
    (IntEq_trans hxy (IntEq_symm hz))

theorem edgeCrossingUp_collinear_split
    (a b : RatComplex) (t : Rat)
    (ht0 : ratLt ratZero t) (ht1 : ratLt t ratOne) :
    IntEq
      (IntAdd
        (edgeCrossingUp { source := a, target := lerpPoint a b t })
        (edgeCrossingUp { source := lerpPoint a b t, target := b }))
      (edgeCrossingUp { source := a, target := b }) := by
  let c := lerpPoint a b t
  change
    IntEq
      (IntAdd
        (edgeCrossingUp { source := a, target := c })
        (edgeCrossingUp { source := c, target := b }))
      (edgeCrossingUp { source := a, target := b })
  cases ratLe_decidable a.im ratZero with
  | inl aNonpos =>
      cases ratLe_decidable b.im ratZero with
      | inl bNonpos =>
          have cNonpos : ratLe c.im ratZero := by
            unfold c
            exact lerp_im_nonpositive_of_endpoints_nonpositive
              a b t ht0 ht1 aNonpos bNonpos
          have leftA := edgeCrossingUp_zero_of_both_nonpositive
            (source := a) (target := c) aNonpos cNonpos
          have leftB := edgeCrossingUp_zero_of_both_nonpositive
            (source := c) (target := b) cNonpos bNonpos
          have whole := edgeCrossingUp_zero_of_both_nonpositive
            (source := a) (target := b) aNonpos bNonpos
          exact edgeCrossingUp_sum_from_values leftA leftB whole
            (IntAdd_zero_left intZero)
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
                edgeCrossingUp_zero_of_source_nonpositive_num_nonpositive
                  (source := a) (target := c) aNonpos numACNonpos
              have leftB :=
                edgeCrossingUp_zero_of_target_positive_num_nonpositive
                  (source := c) (target := b) bPos numCBNonpos
              have whole :=
                edgeCrossingUp_zero_of_source_nonpositive_num_nonpositive
                  (source := a) (target := b) aNonpos numNonpos
              exact edgeCrossingUp_sum_from_values leftA leftB whole
                (IntAdd_zero_left intZero)
          | inr numNotNonpos =>
              have numPos : ratLt ratZero (rayIntersectionNumerator a b) :=
                ratLt_of_not_reverse_le numNotNonpos
              have whole :=
                edgeCrossingUp_one_of_up_conditions
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
                  have leftA := edgeCrossingUp_zero_of_both_nonpositive
                    (source := a) (target := c) aNonpos cNonpos
                  have leftB := edgeCrossingUp_one_of_up_conditions
                    (source := c) (target := b) cNonpos bPos numCBPos
                  exact edgeCrossingUp_sum_from_values leftA leftB whole
                    (IntAdd_zero_left intOne)
              | inr cNotNonpos =>
                  have cPos : ratLt ratZero c.im :=
                    ratLt_of_not_reverse_le cNotNonpos
                  have leftA := edgeCrossingUp_one_of_up_conditions
                    (source := a) (target := c) aNonpos cPos numACPos
                  have leftB := edgeCrossingUp_zero_of_both_positive
                    (source := c) (target := b) cPos bPos
                  exact edgeCrossingUp_sum_from_values leftA leftB whole
                    (IntAdd_zero intOne)
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
                edgeCrossingUp_zero_of_source_positive_num_nonnegative
                  (source := a) (target := c) aPos numACNonneg
              have leftB :=
                edgeCrossingUp_zero_of_target_nonpositive_num_nonnegative
                  (source := c) (target := b) bNonpos numCBNonneg
              have whole :=
                edgeCrossingUp_zero_of_source_positive_num_nonnegative
                  (source := a) (target := b) aPos numNonneg
              exact edgeCrossingUp_sum_from_values leftA leftB whole
                (IntAdd_zero_left intZero)
          | inr numNotNonneg =>
              have numNeg : ratLt (rayIntersectionNumerator a b) ratZero :=
                ratLt_of_not_reverse_le numNotNonneg
              have whole := edgeCrossingUp_neg_one_of_down_conditions
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
                  have leftA := edgeCrossingUp_neg_one_of_down_conditions
                    (source := a) (target := c) cNonpos aPos numACNeg
                  have leftB := edgeCrossingUp_zero_of_both_nonpositive
                    (source := c) (target := b) cNonpos bNonpos
                  exact edgeCrossingUp_sum_from_values leftA leftB whole
                    (IntAdd_zero (IntNeg intOne))
              | inr cNotNonpos =>
                  have cPos : ratLt ratZero c.im :=
                    ratLt_of_not_reverse_le cNotNonpos
                  have leftA := edgeCrossingUp_zero_of_both_positive
                    (source := a) (target := c) aPos cPos
                  have leftB := edgeCrossingUp_neg_one_of_down_conditions
                    (source := c) (target := b) bNonpos cPos numCBNeg
                  exact edgeCrossingUp_sum_from_values leftA leftB whole
                    (IntAdd_zero_left (IntNeg intOne))
      | inr bNotNonpos =>
          have bPos : ratLt ratZero b.im :=
            ratLt_of_not_reverse_le bNotNonpos
          have cPos : ratLt ratZero c.im := by
            unfold c
            exact lerp_im_positive_of_endpoints_positive
              a b t ht0 ht1 aPos bPos
          have leftA := edgeCrossingUp_zero_of_both_positive
            (source := a) (target := c) aPos cPos
          have leftB := edgeCrossingUp_zero_of_both_positive
            (source := c) (target := b) cPos bPos
          have whole := edgeCrossingUp_zero_of_both_positive
            (source := a) (target := b) aPos bPos
          exact edgeCrossingUp_sum_from_values leftA leftB whole
            (IntAdd_zero_left intZero)

theorem sumEdgeCrossingsUp_subdivide_one
    (pre post : List OrientedSegment)
    (a b : RatComplex) (t : Rat)
    (ht0 : ratLt ratZero t) (ht1 : ratLt t ratOne) :
    IntEq
      (sumEdgeCrossingsUp
        (pre ++
          ({ source := a, target := lerpPoint a b t } ::
            { source := lerpPoint a b t, target := b } :: post)))
      (sumEdgeCrossingsUp
        (pre ++ ({ source := a, target := b } :: post))) := by
  let c := lerpPoint a b t
  let first : OrientedSegment := { source := a, target := c }
  let second : OrientedSegment := { source := c, target := b }
  let whole : OrientedSegment := { source := a, target := b }
  change
    IntEq
      (sumEdgeCrossingsUp (pre ++ (first :: second :: post)))
      (sumEdgeCrossingsUp (pre ++ (whole :: post)))
  have leftAppend :
      IntEq (sumEdgeCrossingsUp (pre ++ (first :: second :: post)))
        (IntAdd (sumEdgeCrossingsUp pre)
          (sumEdgeCrossingsUp (first :: second :: post))) :=
    sumEdgeCrossingsUp_append pre (first :: second :: post)
  have rightAppend :
      IntEq (sumEdgeCrossingsUp (pre ++ (whole :: post)))
        (IntAdd (sumEdgeCrossingsUp pre)
          (sumEdgeCrossingsUp (whole :: post))) :=
    sumEdgeCrossingsUp_append pre (whole :: post)
  have split :
      IntEq (IntAdd (edgeCrossingUp first) (edgeCrossingUp second))
        (edgeCrossingUp whole) := by
    unfold first second whole c
    exact edgeCrossingUp_collinear_split a b t ht0 ht1
  have tail :
      IntEq (sumEdgeCrossingsUp (first :: second :: post))
        (sumEdgeCrossingsUp (whole :: post)) := by
    change
      IntEq
        (IntAdd (edgeCrossingUp first)
          (IntAdd (edgeCrossingUp second) (sumEdgeCrossingsUp post)))
        (IntAdd (edgeCrossingUp whole) (sumEdgeCrossingsUp post))
    exact IntEq_trans
      (IntEq_symm
        (IntAdd_assoc (edgeCrossingUp first)
          (edgeCrossingUp second) (sumEdgeCrossingsUp post)))
      (IntAdd_respects split (IntEq_refl (sumEdgeCrossingsUp post)))
  have withPre :
      IntEq
        (IntAdd (sumEdgeCrossingsUp pre)
          (sumEdgeCrossingsUp (first :: second :: post)))
        (IntAdd (sumEdgeCrossingsUp pre)
          (sumEdgeCrossingsUp (whole :: post))) :=
    IntAdd_respects (IntEq_refl (sumEdgeCrossingsUp pre)) tail
  exact IntEq_trans leftAppend (IntEq_trans withPre (IntEq_symm rightAppend))

end BEDC.Derived.RHRoute.RationalPolygonEdgeSubdivision
