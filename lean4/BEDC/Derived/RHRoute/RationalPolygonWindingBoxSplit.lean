import BEDC.Derived.RHRoute.RationalPolygonWindingReversal

namespace BEDC.Derived.RHRoute.RationalPolygonWinding

open BEDC.Derived.RationalUp

private theorem sumEdgeCrossingsUp_singleton
    (edge : OrientedSegment) :
    IntEq (sumEdgeCrossingsUp [edge]) (edgeCrossingUp edge) := by
  change IntEq (IntAdd (edgeCrossingUp edge) intZero) (edgeCrossingUp edge)
  exact IntAdd_zero (edgeCrossingUp edge)

private theorem sumEdgeCrossingsUp_append_singleton
    (left : List OrientedSegment)
    (edge : OrientedSegment) :
    IntEq (sumEdgeCrossingsUp (left ++ [edge]))
      (IntAdd (sumEdgeCrossingsUp left) (edgeCrossingUp edge)) := by
  exact IntEq_trans
    (sumEdgeCrossingsUp_append left [edge])
    (IntAdd_respects
      (IntEq_refl (sumEdgeCrossingsUp left))
      (sumEdgeCrossingsUp_singleton edge))

private theorem IntAdd_cancel_middle_pair
    (x y p q : WindingInteger)
    (cancel : IntEq (IntAdd p q) intZero) :
    IntEq (IntAdd (IntAdd x p) (IntAdd q y)) (IntAdd x y) := by
  have reassocLeft :
      IntEq (IntAdd (IntAdd x p) (IntAdd q y))
        (IntAdd x (IntAdd p (IntAdd q y))) :=
    IntAdd_assoc x p (IntAdd q y)
  have gatherMiddle :
      IntEq (IntAdd x (IntAdd p (IntAdd q y)))
        (IntAdd x (IntAdd (IntAdd p q) y)) :=
    IntAdd_respects
      (IntEq_refl x)
      (IntEq_symm (IntAdd_assoc p q y))
  have cancelMiddle :
      IntEq (IntAdd x (IntAdd (IntAdd p q) y))
        (IntAdd x (IntAdd intZero y)) :=
    IntAdd_respects
      (IntEq_refl x)
      (IntAdd_respects cancel (IntEq_refl y))
  have dropZero :
      IntEq (IntAdd x (IntAdd intZero y)) (IntAdd x y) :=
    IntAdd_respects
      (IntEq_refl x)
      (IntAdd_zero_left y)
  exact IntEq_trans reassocLeft
    (IntEq_trans gatherMiddle
      (IntEq_trans cancelMiddle dropZero))

theorem sumEdgeCrossingsUp_box_split
    (outerL outerR : List OrientedSegment)
    (a b : RatComplex) :
    IntEq (sumEdgeCrossingsUp (outerL ++ outerR))
      (IntAdd
        (sumEdgeCrossingsUp (outerL ++ [{ source := a, target := b }]))
        (sumEdgeCrossingsUp ({ source := b, target := a } :: outerR))) := by
  let forward : OrientedSegment := { source := a, target := b }
  let reverse : OrientedSegment := { source := b, target := a }
  let leftSum : WindingInteger := sumEdgeCrossingsUp outerL
  let rightSum : WindingInteger := sumEdgeCrossingsUp outerR
  let forwardCross : WindingInteger := edgeCrossingUp forward
  let reverseCross : WindingInteger := edgeCrossingUp reverse
  have wholeExpand :
      IntEq (sumEdgeCrossingsUp (outerL ++ outerR))
        (IntAdd leftSum rightSum) := by
    unfold leftSum rightSum
    exact sumEdgeCrossingsUp_append outerL outerR
  have leftExpand :
      IntEq (sumEdgeCrossingsUp (outerL ++ [forward]))
        (IntAdd leftSum forwardCross) := by
    unfold leftSum forwardCross
    exact sumEdgeCrossingsUp_append_singleton outerL forward
  have rightExpand :
      IntEq (sumEdgeCrossingsUp (reverse :: outerR))
        (IntAdd reverseCross rightSum) := by
    unfold reverseCross rightSum
    change IntEq
      (IntAdd (edgeCrossingUp reverse) (sumEdgeCrossingsUp outerR))
      (IntAdd (edgeCrossingUp reverse) (sumEdgeCrossingsUp outerR))
    exact IntEq_refl _
  have rhsExpand :
      IntEq
        (IntAdd
          (sumEdgeCrossingsUp (outerL ++ [forward]))
          (sumEdgeCrossingsUp (reverse :: outerR)))
        (IntAdd
          (IntAdd leftSum forwardCross)
          (IntAdd reverseCross rightSum)) :=
    IntAdd_respects leftExpand rightExpand
  have sharedCancel :
      IntEq (IntAdd forwardCross reverseCross) intZero := by
    unfold forwardCross reverseCross forward reverse
    exact edgeCrossingUp_reverse_cancel a b
  have rhsCollapse :
      IntEq
        (IntAdd
          (IntAdd leftSum forwardCross)
          (IntAdd reverseCross rightSum))
        (IntAdd leftSum rightSum) :=
    IntAdd_cancel_middle_pair leftSum rightSum
      forwardCross reverseCross sharedCancel
  exact IntEq_trans wholeExpand
    (IntEq_symm (IntEq_trans rhsExpand rhsCollapse))

end BEDC.Derived.RHRoute.RationalPolygonWinding
