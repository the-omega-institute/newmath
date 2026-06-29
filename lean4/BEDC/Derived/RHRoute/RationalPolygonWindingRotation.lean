import BEDC.Derived.RHRoute.RationalPolygonWinding

namespace BEDC.Derived.RHRoute.RationalPolygonWinding

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

theorem closedEdgesFrom_append_last
    (newFirst oldFirst previous : RatComplex)
    (vertices : List RatComplex) :
    closedEdgesFrom newFirst previous (vertices ++ [oldFirst]) =
      closedEdgesFrom oldFirst previous vertices ++
        [{ source := oldFirst, target := newFirst }] := by
  induction vertices generalizing previous with
  | nil =>
      rfl
  | cons vertex rest ih =>
      change
        { source := previous, target := vertex } ::
          closedEdgesFrom newFirst vertex (rest ++ [oldFirst]) =
        { source := previous, target := vertex } ::
          (closedEdgesFrom oldFirst vertex rest ++
            [{ source := oldFirst, target := newFirst }])
      rw [ih vertex]

theorem closedEdges_rotate_one_cons
    (v0 v1 : RatComplex) (tail : List RatComplex) :
    closedEdges ((v1 :: tail) ++ [v0]) =
      closedEdgesFrom v0 v1 tail ++
        [{ source := v0, target := v1 }] := by
  change
    closedEdgesFrom v1 v1 (tail ++ [v0]) =
      closedEdgesFrom v0 v1 tail ++
        [{ source := v0, target := v1 }]
  exact closedEdgesFrom_append_last v1 v0 v1 tail

theorem sumEdgeCrossingsUp_singleton
    (edge : OrientedSegment) :
    IntEq (sumEdgeCrossingsUp [edge]) (edgeCrossingUp edge) := by
  change
    IntEq (IntAdd (edgeCrossingUp edge) intZero)
      (edgeCrossingUp edge)
  exact IntAdd_zero (edgeCrossingUp edge)

theorem sumEdgeCrossingsUp_rotate_one
    (edge : OrientedSegment) (edges : List OrientedSegment) :
    IntEq (sumEdgeCrossingsUp (edges ++ [edge]))
      (sumEdgeCrossingsUp (edge :: edges)) := by
  change
    IntEq (sumEdgeCrossingsUp (edges ++ [edge]))
      (IntAdd (edgeCrossingUp edge) (sumEdgeCrossingsUp edges))
  have split :
      IntEq (sumEdgeCrossingsUp (edges ++ [edge]))
        (IntAdd (sumEdgeCrossingsUp edges)
          (sumEdgeCrossingsUp [edge])) :=
    sumEdgeCrossingsUp_append edges [edge]
  have collapseTail :
      IntEq
        (IntAdd (sumEdgeCrossingsUp edges)
          (sumEdgeCrossingsUp [edge]))
        (IntAdd (sumEdgeCrossingsUp edges) (edgeCrossingUp edge)) :=
    IntAdd_respects (IntEq_refl (sumEdgeCrossingsUp edges))
      (sumEdgeCrossingsUp_singleton edge)
  have commute :
      IntEq
        (IntAdd (sumEdgeCrossingsUp edges) (edgeCrossingUp edge))
        (IntAdd (edgeCrossingUp edge) (sumEdgeCrossingsUp edges)) :=
    IntAdd_comm (sumEdgeCrossingsUp edges) (edgeCrossingUp edge)
  exact IntEq_trans split (IntEq_trans collapseTail commute)

theorem computedWindingUp_cyclic_rotate_one
    (v0 : RatComplex) (rest : List RatComplex) :
    IntEq (computedWindingUp ⟨v0 :: rest⟩)
      (computedWindingUp ⟨rest ++ [v0]⟩) := by
  cases rest with
  | nil =>
      unfold computedWindingUp polygonEdges closedEdges
      exact IntEq_refl _
  | cons v1 tail =>
      unfold computedWindingUp polygonEdges closedEdges
      change
        IntEq
          (sumEdgeCrossingsUp
            ({ source := v0, target := v1 } ::
              closedEdgesFrom v0 v1 tail))
          (sumEdgeCrossingsUp
            (closedEdgesFrom v1 v1 (tail ++ [v0])))
      rw [closedEdgesFrom_append_last v1 v0 v1 tail]
      exact IntEq_symm
        (sumEdgeCrossingsUp_rotate_one
          { source := v0, target := v1 }
          (closedEdgesFrom v0 v1 tail))

end BEDC.Derived.RHRoute.RationalPolygonWinding
