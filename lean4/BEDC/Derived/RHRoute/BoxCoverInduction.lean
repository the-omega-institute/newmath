import BEDC.Boundary.ArgumentPrincipleConstructive
import BEDC.Derived.RHRoute.ArgumentPrincipleUp
import BEDC.Derived.RHRoute.RationalPolygonWinding

namespace BEDC.Derived.RHRoute.BoxCoverInduction

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator
open BEDC.Derived.RHRoute.ArgumentPrincipleUp
open BEDC.Derived.RHRoute.RationalPolygonWinding

abbrev RationalBox : Type :=
  BEDC.Derived.RHRoute.ArgumentPrincipleUp.RationalRectangle

abbrev RationalBoundaryPolygon : Type :=
  BEDC.Derived.RHRoute.RationalPolygonWinding.RationalPolygon

abbrev OrientedBoundarySegment : Type :=
  BEDC.Derived.RHRoute.RationalPolygonWinding.OrientedSegment

abbrev BoxPoint : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

abbrev WindingInteger : Type :=
  BEDC.Derived.RHRoute.RationalPolygonWinding.WindingInteger

def BoxSubset (inner outer : RationalBox) : Prop :=
  (z : BoxPoint) ->
    RectContainsPoint inner z -> RectContainsPoint outer z

def BoundaryRectMatchesBox
    (rect : BEDC.Boundary.ArgumentPrincipleConstructive.RatRect)
    (box : RationalBox) : Prop :=
  rect.re.lo = box.left ∧
    rect.re.hi = box.right ∧
      rect.im.lo = box.bottom ∧
        rect.im.hi = box.top

inductive ListMember {α : Type u} (x : α) : List α -> Type u where
  | head {rest : List α} :
      ListMember x (x :: rest)
  | tail {y : α} {rest : List α} :
      ListMember x rest -> ListMember x (y :: rest)

structure BoxCoverHit (boxes : List RationalBox) (z : BoxPoint) where
  box : RationalBox
  member : ListMember box boxes
  inBox : RectContainsPoint box z

structure FiniteRationalBoxCover (parent : RationalBox) where
  parentWellformed : RectWellFormed parent
  boxes : List RationalBox
  childWellformed :
    (box : RationalBox) -> ListMember box boxes -> RectWellFormed box
  childSubset :
    (box : RationalBox) -> ListMember box boxes -> BoxSubset box parent
  covers :
    (z : BoxPoint) -> RectContainsPoint parent z -> BoxCoverHit boxes z

def rectangleBoundaryPolygon (rect : RationalBox) :
    RationalBoundaryPolygon :=
  { vertices :=
      [ rectangleBottomLeft rect,
        rectangleBottomRight rect,
        rectangleTopRight rect,
        rectangleTopLeft rect ] }

structure BoxWindingCell where
  rect : RationalBox
  wellformed : RectWellFormed rect
  polygon : RationalBoundaryPolygon
  polygonEqBoundary : polygon = rectangleBoundaryPolygon rect
  winding : WindingInteger
  windingEq : IntEq (computedWindingUp polygon) winding

def computedBoxWindingCell
    (rect : RationalBox) (wellformed : RectWellFormed rect) :
    BoxWindingCell :=
  { rect := rect
    wellformed := wellformed
    polygon := rectangleBoundaryPolygon rect
    polygonEqBoundary := rfl
    winding := computedWindingUp (rectangleBoundaryPolygon rect)
    windingEq := IntEq_refl (computedWindingUp (rectangleBoundaryPolygon rect)) }

def windingCellRects : List BoxWindingCell -> List RationalBox
  | [] => []
  | cell :: rest => cell.rect :: windingCellRects rest

def windingCellEdges : List BoxWindingCell -> List OrientedBoundarySegment
  | [] => []
  | cell :: rest => polygonEdges cell.polygon ++ windingCellEdges rest

def sumCellWindings : List BoxWindingCell -> WindingInteger
  | [] => intZero
  | cell :: rest => IntAdd cell.winding (sumCellWindings rest)

theorem sumCellWindings_append
    (left right : List BoxWindingCell) :
    IntEq (sumCellWindings (left ++ right))
      (IntAdd (sumCellWindings left) (sumCellWindings right)) := by
  induction left with
  | nil =>
      change IntEq (sumCellWindings right)
        (IntAdd intZero (sumCellWindings right))
      exact IntEq_symm (IntAdd_zero_left (sumCellWindings right))
  | cons cell rest ih =>
      change IntEq
        (IntAdd cell.winding (sumCellWindings (rest ++ right)))
        (IntAdd (IntAdd cell.winding (sumCellWindings rest))
          (sumCellWindings right))
      have inner :
          IntEq
            (IntAdd cell.winding (sumCellWindings (rest ++ right)))
            (IntAdd cell.winding
              (IntAdd (sumCellWindings rest) (sumCellWindings right))) :=
        IntAdd_respects (IntEq_refl cell.winding) ih
      exact IntEq_trans inner
        (IntEq_symm (IntAdd_assoc cell.winding
          (sumCellWindings rest) (sumCellWindings right)))

theorem windingCellEdges_sum
    (cells : List BoxWindingCell) :
    IntEq (sumEdgeCrossingsUp (windingCellEdges cells))
      (sumCellWindings cells) := by
  induction cells with
  | nil =>
      exact IntEq_refl intZero
  | cons cell rest ih =>
      unfold windingCellEdges sumCellWindings
      have split :
          IntEq
            (sumEdgeCrossingsUp (polygonEdges cell.polygon ++
              windingCellEdges rest))
            (IntAdd (sumEdgeCrossingsUp (polygonEdges cell.polygon))
              (sumEdgeCrossingsUp (windingCellEdges rest))) :=
        sumEdgeCrossingsUp_append (polygonEdges cell.polygon)
          (windingCellEdges rest)
      have cellEq :
          IntEq (sumEdgeCrossingsUp (polygonEdges cell.polygon))
            cell.winding := by
        exact cell.windingEq
      have replace :
          IntEq
            (IntAdd (sumEdgeCrossingsUp (polygonEdges cell.polygon))
              (sumEdgeCrossingsUp (windingCellEdges rest)))
            (IntAdd cell.winding (sumCellWindings rest)) :=
        IntAdd_respects cellEq ih
      exact IntEq_trans split replace

structure CoverEdgeDecomposition
    (parent : RationalBoundaryPolygon) (cells : List BoxWindingCell) where
  edgesEq : polygonEdges parent = windingCellEdges cells

theorem cover_winding_additive_from_edge_decomposition
    {parent : RationalBoundaryPolygon} {cells : List BoxWindingCell}
    (decomposition : CoverEdgeDecomposition parent cells) :
    IntEq (computedWindingUp parent) (sumCellWindings cells) := by
  unfold computedWindingUp
  rw [decomposition.edgesEq]
  exact windingCellEdges_sum cells

theorem pair_cover_winding_additive_from_edge_decomposition
    {whole : RationalBoundaryPolygon}
    (left right : BoxWindingCell)
    (decomposition :
      BEDC.Derived.RHRoute.RationalPolygonWinding.EdgeDecomposition
        whole left.polygon right.polygon) :
    IntEq (computedWindingUp whole)
      (IntAdd left.winding right.winding) := by
  have base :
      IntEq (computedWindingUp whole)
        (IntAdd (computedWindingUp left.polygon)
          (computedWindingUp right.polygon)) :=
    winding_add_append decomposition
  have replace :
      IntEq
        (IntAdd (computedWindingUp left.polygon)
          (computedWindingUp right.polygon))
        (IntAdd left.winding right.winding) :=
    IntAdd_respects left.windingEq right.windingEq
  exact IntEq_trans base replace

structure BoxCoverSplit (parent : BoxWindingCell) where
  cover : FiniteRationalBoxCover parent.rect
  children : List BoxWindingCell
  childRectsEq : windingCellRects children = cover.boxes
  edgeDecomposition : CoverEdgeDecomposition parent.polygon children

theorem split_parent_winding_eq_child_sum
    {parent : BoxWindingCell} (split : BoxCoverSplit parent) :
    IntEq parent.winding (sumCellWindings split.children) := by
  exact IntEq_trans (IntEq_symm parent.windingEq)
    (cover_winding_additive_from_edge_decomposition split.edgeDecomposition)

mutual

inductive CoverRefinement : BoxWindingCell -> WindingInteger -> Type where
  | leaf (cell : BoxWindingCell) :
      CoverRefinement cell cell.winding
  | split {parent : BoxWindingCell} {total : WindingInteger}
      (splitData : BoxCoverSplit parent)
      (children : CoverRefinementList splitData.children total) :
      CoverRefinement parent total

inductive CoverRefinementList :
    List BoxWindingCell -> WindingInteger -> Type where
  | nil : CoverRefinementList [] intZero
  | cons {cell : BoxWindingCell} {cells : List BoxWindingCell}
      {headTotal tailTotal : WindingInteger}
      (head : CoverRefinement cell headTotal)
      (tail : CoverRefinementList cells tailTotal) :
      CoverRefinementList (cell :: cells)
        (IntAdd headTotal tailTotal)

end

mutual

def CoverRefinement.sound :
    {cell : BoxWindingCell} -> {total : WindingInteger} ->
      CoverRefinement cell total -> IntEq cell.winding total
  | _, _, CoverRefinement.leaf cell =>
      IntEq_refl cell.winding
  | _, _, CoverRefinement.split splitData children =>
      IntEq_trans (split_parent_winding_eq_child_sum splitData)
        (CoverRefinementList.sound children)

def CoverRefinementList.sound :
    {cells : List BoxWindingCell} -> {total : WindingInteger} ->
      CoverRefinementList cells total ->
        IntEq (sumCellWindings cells) total
  | _, _, CoverRefinementList.nil =>
      IntEq_refl intZero
  | _, _, CoverRefinementList.cons head tail =>
      IntAdd_respects (CoverRefinement.sound head)
        (CoverRefinementList.sound tail)

end

def BoxCoverSplit.childSumData
    {parent : BoxWindingCell} (split : BoxCoverSplit parent) :
    PSigma (fun total : WindingInteger =>
      IntEq parent.winding total) :=
  ⟨sumCellWindings split.children,
    split_parent_winding_eq_child_sum split⟩

def CoverRefinement.totalData
    {cell : BoxWindingCell} {total : WindingInteger}
    (refinement : CoverRefinement cell total) :
    PSigma (fun refinedTotal : WindingInteger =>
      IntEq cell.winding refinedTotal) :=
  ⟨total, CoverRefinement.sound refinement⟩

structure ArgumentPrincipleBoundaryHandoff
    (cell : BoxWindingCell) where
  interface :
    BEDC.Boundary.ArgumentPrincipleConstructive.ZetaBoundaryInterface
  rect : BEDC.Boundary.ArgumentPrincipleConstructive.RatRect
  rectMatchesCell : BoundaryRectMatchesBox rect cell.rect
  boundaryApart : interface.apartFromZeroOnBoundary interface.zeta rect

def ArgumentPrincipleBoundaryHandoff.zeroCountTarget
    {cell : BoxWindingCell}
    (handoff : ArgumentPrincipleBoundaryHandoff cell) : Prop :=
  BEDC.Boundary.ArgumentPrincipleConstructive.argumentPrinciple_rect
    handoff.interface handoff.rect handoff.boundaryApart

structure WindingZeroCountBoundaryRow (cell : BoxWindingCell) where
  handoff : ArgumentPrincipleBoundaryHandoff cell
  target :
    ArgumentPrincipleBoundaryHandoff.zeroCountTarget handoff

end BEDC.Derived.RHRoute.BoxCoverInduction
