import BEDC.Derived.RHRoute.ZetaBoxEvaluator

namespace BEDC.Derived.RHRoute.RationalPolygonWinding

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

abbrev WindingInteger : Type :=
  BEDC.Derived.PrimeUp.IntegerUp

structure RationalPolygon where
  vertices : List RatComplex

structure OrientedSegment where
  source : RatComplex
  target : RatComplex

def ratStrictPositiveBool (q : Rat) : Bool :=
  ratLtBool ratZero q

def ratStrictNegativeBool (q : Rat) : Bool :=
  ratLtBool q ratZero

def ratNonPositiveBool (q : Rat) : Bool :=
  ratLeBool q ratZero

def rayIntersectionNumerator (source target : RatComplex) : Rat :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub
    (ratMul source.re target.im) (ratMul target.re source.im)

def upwardPositiveRayCrossingBool (source target : RatComplex) : Bool :=
  ratNonPositiveBool source.im &&
    ratStrictPositiveBool target.im &&
      ratStrictPositiveBool (rayIntersectionNumerator source target)

def downwardPositiveRayCrossingBool (source target : RatComplex) : Bool :=
  ratNonPositiveBool target.im &&
    ratStrictPositiveBool source.im &&
      ratStrictNegativeBool (rayIntersectionNumerator source target)

def edgeCrossing (edge : OrientedSegment) : Int :=
  if upwardPositiveRayCrossingBool edge.source edge.target then
    1
  else if downwardPositiveRayCrossingBool edge.source edge.target then
    -1
  else
    0

def edgeCrossingUp (edge : OrientedSegment) : WindingInteger :=
  if upwardPositiveRayCrossingBool edge.source edge.target then
    intOne
  else if downwardPositiveRayCrossingBool edge.source edge.target then
    IntNeg intOne
  else
    intZero

def closedEdgesFrom (first previous : RatComplex) :
    List RatComplex -> List OrientedSegment
  | [] => [{ source := previous, target := first }]
  | vertex :: rest =>
      { source := previous, target := vertex } ::
        closedEdgesFrom first vertex rest

def closedEdges : List RatComplex -> List OrientedSegment
  | [] => []
  | first :: rest => closedEdgesFrom first first rest

def polygonEdges (polygon : RationalPolygon) : List OrientedSegment :=
  closedEdges polygon.vertices

def sumEdgeCrossings : List OrientedSegment -> Int
  | [] => 0
  | edge :: rest => edgeCrossing edge + sumEdgeCrossings rest

def computedWinding (polygon : RationalPolygon) : Int :=
  sumEdgeCrossings (polygonEdges polygon)

def sumEdgeCrossingsUp : List OrientedSegment -> WindingInteger
  | [] => intZero
  | edge :: rest => IntAdd (edgeCrossingUp edge) (sumEdgeCrossingsUp rest)

def computedWindingUp (polygon : RationalPolygon) : WindingInteger :=
  sumEdgeCrossingsUp (polygonEdges polygon)

def sumIntList : List Int -> Int
  | [] => 0
  | value :: rest => value + sumIntList rest

def crossingProfile : List OrientedSegment -> List Int
  | [] => []
  | edge :: rest => edgeCrossing edge :: crossingProfile rest

theorem sumEdgeCrossingsUp_append
    (left right : List OrientedSegment) :
    IntEq (sumEdgeCrossingsUp (left ++ right))
      (IntAdd (sumEdgeCrossingsUp left) (sumEdgeCrossingsUp right)) := by
  induction left with
  | nil =>
      change IntEq (sumEdgeCrossingsUp right)
        (IntAdd intZero (sumEdgeCrossingsUp right))
      exact IntEq_symm (IntAdd_zero_left (sumEdgeCrossingsUp right))
  | cons edge rest ih =>
      change IntEq
        (IntAdd (edgeCrossingUp edge) (sumEdgeCrossingsUp (rest ++ right)))
        (IntAdd
          (IntAdd (edgeCrossingUp edge) (sumEdgeCrossingsUp rest))
          (sumEdgeCrossingsUp right))
      have inner :
          IntEq
            (IntAdd (edgeCrossingUp edge) (sumEdgeCrossingsUp (rest ++ right)))
            (IntAdd (edgeCrossingUp edge)
              (IntAdd (sumEdgeCrossingsUp rest) (sumEdgeCrossingsUp right))) :=
        IntAdd_respects (IntEq_refl (edgeCrossingUp edge)) ih
      exact IntEq_trans inner
        (IntEq_symm (IntAdd_assoc (edgeCrossingUp edge)
          (sumEdgeCrossingsUp rest) (sumEdgeCrossingsUp right)))

theorem sumEdgeCrossings_profile
    (edges : List OrientedSegment) :
    sumEdgeCrossings edges = sumIntList (crossingProfile edges) := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      change
        edgeCrossing edge + sumEdgeCrossings rest =
          edgeCrossing edge + sumIntList (crossingProfile rest)
      rw [ih]

theorem sumEdgeCrossings_of_profile_eq
    {left right : List OrientedSegment}
    (profile_eq : crossingProfile left = crossingProfile right) :
    sumEdgeCrossings left = sumEdgeCrossings right := by
  rw [sumEdgeCrossings_profile left, sumEdgeCrossings_profile right,
    profile_eq]

structure EdgeDecomposition
    (whole left right : RationalPolygon) where
  edges_eq :
    polygonEdges whole = polygonEdges left ++ polygonEdges right

theorem winding_add_append
    {whole left right : RationalPolygon}
    (decomposition : EdgeDecomposition whole left right) :
    IntEq (computedWindingUp whole)
      (IntAdd (computedWindingUp left) (computedWindingUp right)) := by
  unfold computedWindingUp
  rw [decomposition.edges_eq]
  exact sumEdgeCrossingsUp_append (polygonEdges left) (polygonEdges right)

structure RationalTube where
  reLo : Rat
  reHi : Rat
  imLo : Rat
  imHi : Rat

def pointInTubeBool (point : RatComplex) (tube : RationalTube) : Bool :=
  ratLeBool tube.reLo point.re &&
    ratLeBool point.re tube.reHi &&
      ratLeBool tube.imLo point.im &&
        ratLeBool point.im tube.imHi

def tubeApartOriginBool (tube : RationalTube) : Bool :=
  ratStrictNegativeBool tube.reHi ||
    ratStrictPositiveBool tube.reLo ||
      ratStrictNegativeBool tube.imHi ||
        ratStrictPositiveBool tube.imLo

structure SegmentTubeApart (edge : OrientedSegment) where
  tube : RationalTube
  source_in_tube : pointInTubeBool edge.source tube = true
  target_in_tube : pointInTubeBool edge.target tube = true
  tube_apart_origin : tubeApartOriginBool tube = true

inductive EdgeTubeApartList : List OrientedSegment -> Type where
  | nil : EdgeTubeApartList []
  | cons {edge : OrientedSegment} {rest : List OrientedSegment} :
      SegmentTubeApart edge ->
        EdgeTubeApartList rest ->
          EdgeTubeApartList (edge :: rest)

structure DiscreteWinding (polygon : RationalPolygon) where
  value : Int
  value_eq : value = computedWinding polygon
  apart_edges : EdgeTubeApartList (polygonEdges polygon)

def windingOfTubeApart
    (polygon : RationalPolygon)
    (apart : EdgeTubeApartList (polygonEdges polygon)) :
    DiscreteWinding polygon :=
  { value := computedWinding polygon
    value_eq := rfl
    apart_edges := apart }

def computedWindingData (polygon : RationalPolygon) :
    PSigma (fun value : Int => value = computedWinding polygon) :=
  ⟨computedWinding polygon, rfl⟩

theorem computedWindingData_value
    (polygon : RationalPolygon) :
    (computedWindingData polygon).1 = computedWinding polygon := by
  rfl

structure CertifiedPuncturedPlaneHomotopy
    (source target : RationalPolygon) where
  source_apart : EdgeTubeApartList (polygonEdges source)
  target_apart : EdgeTubeApartList (polygonEdges target)
  crossing_profile_eq :
    crossingProfile (polygonEdges source) =
      crossingProfile (polygonEdges target)

theorem certified_homotopy_winding_invariant
    {source target : RationalPolygon}
    (homotopy : CertifiedPuncturedPlaneHomotopy source target) :
    computedWinding source = computedWinding target := by
  unfold computedWinding
  exact sumEdgeCrossings_of_profile_eq homotopy.crossing_profile_eq

def rho_near_14_1347_winding_payload
    (polygon : RationalPolygon)
    (apart : EdgeTubeApartList (polygonEdges polygon)) :
    PSigma (fun winding : DiscreteWinding polygon =>
      winding.value = computedWinding polygon) :=
  ⟨windingOfTubeApart polygon apart, rfl⟩

end BEDC.Derived.RHRoute.RationalPolygonWinding
