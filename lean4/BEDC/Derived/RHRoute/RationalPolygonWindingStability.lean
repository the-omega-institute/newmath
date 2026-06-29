import BEDC.Derived.RHRoute.RationalPolygonWinding
import BEDC.Derived.RationalOrderArithUp
import BEDC.Derived.LocatedReal.GroundedToleranceKit

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.RationalPolygonWindingStability

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RHRoute.RationalPolygonWinding

abbrev Rat : Type :=
  BEDC.Derived.RationalUp.RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

def pointDistQ (z w : RatComplex) : Rat :=
  ratAdd (ratDist z.re w.re) (ratDist z.im w.im)

def endpointDistWithin (z w : RatComplex) (delta : Rat) : Prop :=
  ratLt (pointDistQ z w) delta

def edgeEndpointsDistWithin
    (edge perturbed : OrientedSegment) (delta : Rat) : Prop :=
  endpointDistWithin edge.source perturbed.source delta ∧
    endpointDistWithin edge.target perturbed.target delta

def upperHalfplaneMargin (edge : OrientedSegment) (delta : Rat) : Prop :=
  ratLt ratZero delta ∧
    ratLt ratZero edge.source.im ∧
      ratLt ratZero edge.target.im ∧
        ratLt delta edge.source.im ∧ ratLt delta edge.target.im

def lowerHalfplaneMargin (edge : OrientedSegment) (delta : Rat) : Prop :=
  ratLt ratZero delta ∧
    ratLt edge.source.im ratZero ∧
      ratLt edge.target.im ratZero ∧
        ratLt edge.source.im (ratNeg delta) ∧
          ratLt edge.target.im (ratNeg delta)

def halfplaneMargin (edge : OrientedSegment) (delta : Rat) : Prop :=
  upperHalfplaneMargin edge delta ∨ lowerHalfplaneMargin edge delta

structure MarginPreservingPerturbation
    (edge perturbed : OrientedSegment) (delta : Rat) where
  source_close : endpointDistWithin edge.source perturbed.source delta
  target_close : endpointDistWithin edge.target perturbed.target delta
  edge_margin : halfplaneMargin edge delta

inductive vertexwiseDistWithin :
    List RatComplex -> List RatComplex -> Rat -> Prop where
  | nil {delta : Rat} : vertexwiseDistWithin [] [] delta
  | cons {point perturbed : RatComplex}
      {points perturbedPoints : List RatComplex} {delta : Rat} :
      endpointDistWithin point perturbed delta ->
        vertexwiseDistWithin points perturbedPoints delta ->
          vertexwiseDistWithin
            (point :: points) (perturbed :: perturbedPoints) delta

inductive edgewiseMarginPreserving :
    List OrientedSegment -> List OrientedSegment -> Rat -> Prop where
  | nil {delta : Rat} : edgewiseMarginPreserving [] [] delta
  | cons {edge perturbed : OrientedSegment}
      {edges perturbedEdges : List OrientedSegment} {delta : Rat} :
      MarginPreservingPerturbation edge perturbed delta ->
        edgewiseMarginPreserving edges perturbedEdges delta ->
          edgewiseMarginPreserving
            (edge :: edges) (perturbed :: perturbedEdges) delta

inductive edgeListHalfplaneMargins : List OrientedSegment -> Rat -> Prop where
  | nil {delta : Rat} : edgeListHalfplaneMargins [] delta
  | cons {edge : OrientedSegment} {edges : List OrientedSegment}
      {delta : Rat} :
      halfplaneMargin edge delta ->
        edgeListHalfplaneMargins edges delta ->
          edgeListHalfplaneMargins (edge :: edges) delta

inductive edgewiseDistWithin :
    List OrientedSegment -> List OrientedSegment -> Rat -> Prop where
  | nil {delta : Rat} : edgewiseDistWithin [] [] delta
  | cons {edge perturbed : OrientedSegment}
      {edges perturbedEdges : List OrientedSegment} {delta : Rat} :
      edgeEndpointsDistWithin edge perturbed delta ->
        edgewiseDistWithin edges perturbedEdges delta ->
          edgewiseDistWithin (edge :: edges) (perturbed :: perturbedEdges) delta

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

theorem ratLeBool_true_to_ratLe {x y : Rat} :
    ratLeBool x y = true -> ratLe x y := by
  intro h
  unfold ratLeBool at h
  unfold ratLe BEDC.Derived.RationalUp.intLe
  exact BEDC.Derived.IntUp.pairLe_of_length_order
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (natLeBool_true_to_le h)

theorem ratLtBool_true_to_ratLt {x y : Rat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt BEDC.Derived.RationalUp.intLtUp BEDC.Derived.IntUp.intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le h)

theorem ratLtBool_false_of_not_ratLt {x y : Rat} :
    (ratLt x y -> False) -> ratLtBool x y = false := by
  intro notLt
  cases h : ratLtBool x y with
  | false => rfl
  | true => exact False.elim (notLt (ratLtBool_true_to_ratLt h))

theorem ratLeBool_false_of_not_ratLe {x y : Rat} :
    (ratLe x y -> False) -> ratLeBool x y = false := by
  intro notLe
  cases h : ratLeBool x y with
  | false => rfl
  | true => exact False.elim (notLe (ratLeBool_true_to_ratLe h))

theorem positive_not_nonpositive {q : Rat} :
    ratLt ratZero q -> ratLe q ratZero -> False := by
  intro pos nonpos
  exact ratLt_not_ratLe_reverse pos nonpos

theorem negative_not_positive {q : Rat} :
    ratLt q ratZero -> ratLt ratZero q -> False := by
  intro neg pos
  exact ratLt_not_ratLe_reverse neg (ratLt_to_ratLe pos)

theorem ratLt_respects_local {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> ratLt x y -> ratLt x' y' := by
  intro xx' yy' h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_respects xx' yy' (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_respects (RatEq_symm yy') (RatEq_symm xx') reverse)

theorem imDist_lt_of_endpointDistWithin
    {z w : RatComplex} {delta : Rat}
    (close : endpointDistWithin z w delta) :
    ratLt (ratDist z.im w.im) delta := by
  unfold endpointDistWithin pointDistQ at close
  have reNonneg : ratLe ratZero (ratDist z.re w.re) :=
    ratDist_nonneg z.re w.re
  have lowerRaw :
      ratLe (ratAdd ratZero (ratDist z.im w.im))
        (ratAdd (ratDist z.re w.re) (ratDist z.im w.im)) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := ratZero) (x' := ratDist z.re w.re)
      (y := ratDist z.im w.im) reNonneg
  have lower :
      ratLe (ratDist z.im w.im)
        (ratAdd (ratDist z.re w.re) (ratDist z.im w.im)) :=
    ratLe_respects (ratZero_add_left (ratDist z.im w.im))
      (RatEq_refl _) lowerRaw
  exact ratLe_lt_trans lower close

theorem ratSub_le_ratDist (x y : Rat) :
    ratLe (ratSub x y) (ratDist x y) := by
  unfold ratDist
  exact BEDC.Derived.LocatedReal.ratLe_self_abs (ratSub x y)

theorem ratLe_self_sub_of_nonpositive {x y : Rat} :
    ratLe y ratZero -> ratLe x (ratSub x y) := by
  intro yNonpos
  have negNonneg : ratLe ratZero (ratNeg y) := by
    have subNonneg : ratLe ratZero (ratSub ratZero y) :=
      ratSub_nonneg_of_le yNonpos
    exact ratLe_respects (RatEq_refl _)
      (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg y) subNonneg
  have shifted :
      ratLe (ratAdd x ratZero) (ratAdd x (ratNeg y)) :=
    BEDC.Derived.LocatedReal.ratLe_add_left_mono
      (x := x) (y := ratZero) (y' := ratNeg y) negNonneg
  exact ratLe_respects (ratAdd_zero_right x) (RatEq_refl _) shifted

theorem positive_of_dist_lt_margin
    {x y delta : Rat}
    (margin : ratLt delta x)
    (distLt : ratLt (ratDist x y) delta) :
    ratLt ratZero y := by
  have notNonpos : ratLe y ratZero -> False := by
    intro yNonpos
    have xLeSub : ratLe x (ratSub x y) :=
      ratLe_self_sub_of_nonpositive yNonpos
    have subLeDist : ratLe (ratSub x y) (ratDist x y) :=
      ratSub_le_ratDist x y
    have xLeDist : ratLe x (ratDist x y) :=
      ratLe_trans xLeSub subLeDist
    have deltaLtDist : ratLt delta (ratDist x y) := by
      apply ratLe_not_le_to_ratLt
      · exact ratLe_trans (ratLt_to_ratLe margin) xLeDist
      · intro distLeDelta
        exact ratLt_not_ratLe_reverse margin
          (ratLe_trans xLeDist distLeDelta)
    exact ratLt_not_ratLe_reverse distLt (ratLt_to_ratLe deltaLtDist)
  apply ratLe_not_le_to_ratLt
  · cases ratLe_total ratZero y with
    | inl nonneg => exact nonneg
    | inr nonpos => exact False.elim (notNonpos nonpos)
  · exact notNonpos

theorem negative_of_dist_lt_margin
    {x y delta : Rat}
    (margin : ratLt x (ratNeg delta))
    (distLt : ratLt (ratDist x y) delta) :
    ratLt y ratZero := by
  have rawDelta :
      ratLt (ratSub ratZero (ratNeg delta)) (ratSub ratZero x) :=
    const_sub_strictAnti (a := x) (b := ratNeg delta)
      (c := ratZero) margin
  have leftDelta :
      RatEq (ratSub ratZero (ratNeg delta)) delta :=
    RatEq_trans _ _ _
      (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg (ratNeg delta))
      (BEDC.Derived.LocatedReal.ratNeg_neg_local delta)
  have rightDelta :
      RatEq (ratSub ratZero x) (ratNeg x) :=
    BEDC.Derived.LocatedReal.ratZero_sub_eq_neg x
  have deltaLtNegX : ratLt delta (ratNeg x) :=
    ratLt_respects_local leftDelta rightDelta rawDelta
  have negDistLt :
      ratLt (ratDist (ratNeg x) (ratNeg y)) delta :=
    ratLt_respects_local
      (RatEq_symm (BEDC.Derived.LocatedReal.ratDist_neg x y))
      (RatEq_refl delta) distLt
  have negYPos : ratLt ratZero (ratNeg y) :=
    positive_of_dist_lt_margin deltaLtNegX negDistLt
  have rawY :
      ratLt (ratSub ratZero (ratNeg y)) (ratSub ratZero ratZero) :=
    const_sub_strictAnti (a := ratZero) (b := ratNeg y)
      (c := ratZero) negYPos
  have leftY : RatEq (ratSub ratZero (ratNeg y)) y :=
    RatEq_trans _ _ _
      (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg (ratNeg y))
      (BEDC.Derived.LocatedReal.ratNeg_neg_local y)
  have rightY : RatEq (ratSub ratZero ratZero) ratZero :=
    ratSub_self ratZero
  exact ratLt_respects_local leftY rightY rawY

theorem upwardPositiveRayCrossingBool_false_of_source_positive
    {source target : RatComplex}
    (source_pos : ratLt ratZero source.im) :
    upwardPositiveRayCrossingBool source target = false := by
  unfold upwardPositiveRayCrossingBool ratNonPositiveBool
  rw [ratLeBool_false_of_not_ratLe
    (positive_not_nonpositive source_pos)]
  rfl

theorem downwardPositiveRayCrossingBool_false_of_target_positive
    {source target : RatComplex}
    (target_pos : ratLt ratZero target.im) :
    downwardPositiveRayCrossingBool source target = false := by
  unfold downwardPositiveRayCrossingBool ratNonPositiveBool
  rw [ratLeBool_false_of_not_ratLe
    (positive_not_nonpositive target_pos)]
  rfl

theorem upwardPositiveRayCrossingBool_false_of_target_negative
    {source target : RatComplex}
    (target_neg : ratLt target.im ratZero) :
    upwardPositiveRayCrossingBool source target = false := by
  unfold upwardPositiveRayCrossingBool ratNonPositiveBool ratStrictPositiveBool
  cases h : ratLeBool source.im ratZero with
  | false =>
      rfl
  | true =>
      rw [ratLtBool_false_of_not_ratLt
        (negative_not_positive target_neg)]
      rfl

theorem downwardPositiveRayCrossingBool_false_of_source_negative
    {source target : RatComplex}
    (source_neg : ratLt source.im ratZero) :
    downwardPositiveRayCrossingBool source target = false := by
  unfold downwardPositiveRayCrossingBool ratNonPositiveBool
    ratStrictPositiveBool
  cases h : ratLeBool target.im ratZero with
  | false =>
      rfl
  | true =>
      rw [ratLtBool_false_of_not_ratLt
        (negative_not_positive source_neg)]
      rfl

theorem edgeCrossing_zero_of_upperHalfplane
    {edge : OrientedSegment}
    (source_pos : ratLt ratZero edge.source.im)
    (target_pos : ratLt ratZero edge.target.im) :
    edgeCrossing edge = 0 := by
  unfold edgeCrossing
  rw [upwardPositiveRayCrossingBool_false_of_source_positive source_pos]
  rw [downwardPositiveRayCrossingBool_false_of_target_positive target_pos]
  rfl

theorem edgeCrossing_zero_of_lowerHalfplane
    {edge : OrientedSegment}
    (source_neg : ratLt edge.source.im ratZero)
    (target_neg : ratLt edge.target.im ratZero) :
    edgeCrossing edge = 0 := by
  unfold edgeCrossing
  rw [upwardPositiveRayCrossingBool_false_of_target_negative target_neg]
  rw [downwardPositiveRayCrossingBool_false_of_source_negative source_neg]
  rfl

theorem edgeCrossing_zero_of_upperHalfplaneMargin
    {edge : OrientedSegment} {delta : Rat}
    (margin : upperHalfplaneMargin edge delta) :
    edgeCrossing edge = 0 := by
  unfold upperHalfplaneMargin at margin
  exact edgeCrossing_zero_of_upperHalfplane
    margin.right.left margin.right.right.left

theorem edgeCrossing_zero_of_lowerHalfplaneMargin
    {edge : OrientedSegment} {delta : Rat}
    (margin : lowerHalfplaneMargin edge delta) :
    edgeCrossing edge = 0 := by
  unfold lowerHalfplaneMargin at margin
  exact edgeCrossing_zero_of_lowerHalfplane
    margin.right.left margin.right.right.left

theorem edgeCrossing_zero_of_halfplaneMargin
    {edge : OrientedSegment} {delta : Rat}
    (margin : halfplaneMargin edge delta) :
    edgeCrossing edge = 0 := by
  cases margin with
  | inl upper => exact edgeCrossing_zero_of_upperHalfplaneMargin upper
  | inr lower => exact edgeCrossing_zero_of_lowerHalfplaneMargin lower

theorem edgeCrossing_stable_of_marginPreservingPerturbation
    {edge perturbed : OrientedSegment} {delta : Rat}
    (cert : MarginPreservingPerturbation edge perturbed delta) :
    edgeCrossing edge = edgeCrossing perturbed := by
  cases cert.edge_margin with
  | inl upper =>
      rw [edgeCrossing_zero_of_upperHalfplaneMargin upper]
      have sourcePos : ratLt ratZero perturbed.source.im :=
        positive_of_dist_lt_margin upper.right.right.right.left
          (imDist_lt_of_endpointDistWithin cert.source_close)
      have targetPos : ratLt ratZero perturbed.target.im :=
        positive_of_dist_lt_margin upper.right.right.right.right
          (imDist_lt_of_endpointDistWithin cert.target_close)
      rw [edgeCrossing_zero_of_upperHalfplane sourcePos targetPos]
  | inr lower =>
      rw [edgeCrossing_zero_of_lowerHalfplaneMargin lower]
      have sourceNeg : ratLt perturbed.source.im ratZero :=
        negative_of_dist_lt_margin lower.right.right.right.left
          (imDist_lt_of_endpointDistWithin cert.source_close)
      have targetNeg : ratLt perturbed.target.im ratZero :=
        negative_of_dist_lt_margin lower.right.right.right.right
          (imDist_lt_of_endpointDistWithin cert.target_close)
      rw [edgeCrossing_zero_of_lowerHalfplane sourceNeg targetNeg]

theorem sumEdgeCrossings_eq_of_crossingProfile_eq
    {left right : List OrientedSegment}
    (profile_eq : crossingProfile left = crossingProfile right) :
    sumEdgeCrossings left = sumEdgeCrossings right :=
  sumEdgeCrossings_of_profile_eq profile_eq

theorem computedWinding_of_crossingProfile_eq
    {source target : RationalPolygon}
    (profile_eq :
      crossingProfile (polygonEdges source) =
        crossingProfile (polygonEdges target)) :
    computedWinding source = computedWinding target := by
  unfold computedWinding
  exact sumEdgeCrossings_eq_of_crossingProfile_eq profile_eq

theorem computedWinding_of_sumEdgeCrossings_eq
    {source target : RationalPolygon}
    (sum_eq :
      sumEdgeCrossings (polygonEdges source) =
        sumEdgeCrossings (polygonEdges target)) :
    computedWinding source = computedWinding target := by
  unfold computedWinding
  exact sum_eq

theorem crossingProfile_stable_of_edgewiseMarginPreserving :
    ∀ {edges perturbedEdges : List OrientedSegment} {delta : Rat},
      edgewiseMarginPreserving edges perturbedEdges delta ->
        crossingProfile edges = crossingProfile perturbedEdges
  | [], [], _delta, _certs => rfl
  | [], _ :: _, _delta, certs => by cases certs
  | _ :: _, [], _delta, certs => by cases certs
  | edge :: edges, perturbed :: perturbedEdges, delta, certs => by
      cases certs with
      | cons edgeCert restCert =>
          unfold crossingProfile
          rw [edgeCrossing_stable_of_marginPreservingPerturbation edgeCert]
          rw [crossingProfile_stable_of_edgewiseMarginPreserving restCert]

theorem sumEdgeCrossings_stable_of_edgewiseMarginPreserving
    {edges perturbedEdges : List OrientedSegment} {delta : Rat}
    (certs : edgewiseMarginPreserving edges perturbedEdges delta) :
    sumEdgeCrossings edges = sumEdgeCrossings perturbedEdges :=
  sumEdgeCrossings_eq_of_crossingProfile_eq
    (crossingProfile_stable_of_edgewiseMarginPreserving certs)

theorem computedWinding_stable_of_edgewiseMarginPreserving
    {polygon perturbedPolygon : RationalPolygon} {delta : Rat}
    (certs :
      edgewiseMarginPreserving (polygonEdges polygon)
        (polygonEdges perturbedPolygon) delta) :
    computedWinding polygon = computedWinding perturbedPolygon :=
  computedWinding_of_crossingProfile_eq
    (crossingProfile_stable_of_edgewiseMarginPreserving certs)

theorem edgewiseDistWithin_closedEdgesFrom_of_vertexwise :
    ∀ {first previous first' previous' : RatComplex}
      {vertices vertices' : List RatComplex} {delta : Rat},
      endpointDistWithin first first' delta ->
        endpointDistWithin previous previous' delta ->
          vertexwiseDistWithin vertices vertices' delta ->
              edgewiseDistWithin
                (closedEdgesFrom first previous vertices)
                (closedEdgesFrom first' previous' vertices') delta
  | first, previous, first', previous', [], [], delta,
      firstClose, previousClose, _verticesClose => by
      exact edgewiseDistWithin.cons
        (edge := { source := previous, target := first })
        (perturbed := { source := previous', target := first' })
        (edges := [])
        (perturbedEdges := [])
        ⟨previousClose, firstClose⟩
        edgewiseDistWithin.nil
  | _first, _previous, _first', _previous', _ :: _, [], _delta,
      _firstClose, _previousClose, verticesClose => by
      cases verticesClose
  | _first, _previous, _first', _previous', [], _ :: _, _delta,
      _firstClose, _previousClose, verticesClose => by
      cases verticesClose
  | first, previous, first', previous', vertex :: rest, vertex' :: rest',
      delta, firstClose, previousClose, verticesClose => by
      cases verticesClose with
      | cons vertexClose restClose =>
          exact edgewiseDistWithin.cons
            (edge := { source := previous, target := vertex })
            (perturbed := { source := previous', target := vertex' })
            ⟨previousClose, vertexClose⟩
            (edgewiseDistWithin_closedEdgesFrom_of_vertexwise
              firstClose vertexClose restClose)

theorem edgewiseDistWithin_polygonEdges_of_vertexwise
    {polygon perturbedPolygon : RationalPolygon} {delta : Rat}
    (verticesClose :
      vertexwiseDistWithin polygon.vertices perturbedPolygon.vertices delta) :
    edgewiseDistWithin (polygonEdges polygon)
      (polygonEdges perturbedPolygon) delta := by
  unfold polygonEdges closedEdges
  cases hP : polygon.vertices with
  | nil =>
      cases hQ : perturbedPolygon.vertices with
      | nil => exact edgewiseDistWithin.nil
      | cons first' rest' =>
          rw [hP, hQ] at verticesClose
          cases verticesClose
  | cons first rest =>
      cases hQ : perturbedPolygon.vertices with
      | nil =>
          rw [hP, hQ] at verticesClose
          cases verticesClose
      | cons first' rest' =>
          rw [hP, hQ] at verticesClose
          cases verticesClose with
          | cons firstClose restClose =>
              exact edgewiseDistWithin_closedEdgesFrom_of_vertexwise
                firstClose firstClose restClose

theorem edgewiseMarginPreserving_of_dist_and_margins :
    ∀ {edges perturbedEdges : List OrientedSegment} {delta : Rat},
      edgewiseDistWithin edges perturbedEdges delta ->
        edgeListHalfplaneMargins edges delta ->
          edgewiseMarginPreserving edges perturbedEdges delta
  | [], [], _delta, _close, _leftMargins => edgewiseMarginPreserving.nil
  | [], _ :: _, _delta, close, _leftMargins => by
      cases close
  | _ :: _, [], _delta, close, _leftMargins => by
      cases close
  | edge :: edges, perturbed :: perturbedEdges, delta,
      close, leftMargins => by
      cases close with
      | cons endpointsClose restClose =>
          cases leftMargins with
          | cons edgeMargin restMargins =>
              exact edgewiseMarginPreserving.cons
                { source_close := endpointsClose.left
                  target_close := endpointsClose.right
                  edge_margin := edgeMargin }
                (edgewiseMarginPreserving_of_dist_and_margins
                  restClose restMargins)

theorem computedWinding_stable_of_vertexwise_halfplaneMargins
    {polygon perturbedPolygon : RationalPolygon} {delta : Rat}
    (verticesClose :
      vertexwiseDistWithin polygon.vertices perturbedPolygon.vertices delta)
    (polygonMargins :
      edgeListHalfplaneMargins (polygonEdges polygon) delta) :
    computedWinding polygon = computedWinding perturbedPolygon :=
  computedWinding_stable_of_edgewiseMarginPreserving
    (edgewiseMarginPreserving_of_dist_and_margins
      (edgewiseDistWithin_polygonEdges_of_vertexwise verticesClose)
      polygonMargins)

end BEDC.Derived.RHRoute.RationalPolygonWindingStability
