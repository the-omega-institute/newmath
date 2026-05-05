import BEDC.Derived.VecSpaceUp
import BEDC.Derived.MetricUp

namespace BEDC.Derived.ErrorCodeUp

open BEDC.FKernel.Hist
open BEDC.Derived.VecSpaceUp
open BEDC.Derived.MetricUp

def ErrorCodeSingletonCodeword (h : BHist) : Prop :=
  VecSpaceSingletonCarrier h ∧ VecSpaceSingletonClassifier h BHist.Empty

def ErrorCodeSingletonWithinRadius (c r t : BHist) : Prop :=
  VecSpaceSingletonClassifier c BHist.Empty ∧ hsame r t ∧ VecSpaceSingletonCarrier t

theorem ErrorCodeSingleton_unique_decoding_radius {c1 c2 r t : BHist} :
    ErrorCodeSingletonCodeword c1 ->
      ErrorCodeSingletonCodeword c2 ->
        ErrorCodeSingletonWithinRadius c1 r t ->
          ErrorCodeSingletonWithinRadius c2 r t ->
            hsame t BHist.Empty -> VecSpaceSingletonClassifier c1 c2 := by
  intro codewordLeft codewordRight radiusLeft radiusRight targetEmpty
  have receivedEmpty : hsame r BHist.Empty :=
    hsame_trans radiusLeft.right.left targetEmpty
  have radiusRightEndpoint : hsame r BHist.Empty :=
    hsame_trans radiusRight.right.left radiusRight.right.right
  have leftEmpty : hsame c1 BHist.Empty :=
    hsame_trans codewordLeft.left radiusLeft.left.right.left
  have rightEmpty : hsame c2 BHist.Empty :=
    hsame_trans codewordRight.left radiusRight.left.right.left
  have sameCodewords : hsame c1 c2 :=
    hsame_trans leftEmpty
      (hsame_trans (hsame_symm receivedEmpty)
        (hsame_trans radiusRightEndpoint (hsame_symm rightEmpty)))
  exact And.intro leftEmpty (And.intro rightEmpty sameCodewords)

structure ErrorCodeMinimumDistanceInterface where
  Code : BHist -> Prop
  rho : BHist -> BHist -> Prop
  dist : BHist -> BHist -> Nat
  distLedger : BHist -> BHist -> BHist
  minDistance : Nat
  radius : Nat
  minDistance_pos : 0 < minDistance
  radius_bound : radius + radius < minDistance
  dist_symm : forall {x y : BHist}, dist x y = dist y x
  dist_triangle : forall {x y z : BHist}, dist x z <= dist x y + dist y z
  dist_metric : forall {x y : BHist}, Code x -> Code y ->
    MetricDistanceWitness x y (distLedger x y)
  min_distance_sound : forall {x y : BHist}, Code x -> Code y ->
    dist x y < minDistance -> rho x y

theorem ErrorCode_unique_decoding_radius (C : ErrorCodeMinimumDistanceInterface)
    {c1 c2 r : BHist} :
    C.Code c1 -> C.Code c2 -> C.dist c1 r <= C.radius -> C.dist c2 r <= C.radius ->
      C.rho c1 c2 ∧ exists d12 : BHist, MetricDistanceWitness c1 c2 d12 := by
  intro codeC1 codeC2 nearC1 nearC2
  have triangle :
      C.dist c1 c2 <= C.dist c1 r + C.dist c2 r := by
    have raw := C.dist_triangle (x := c1) (y := r) (z := c2)
    exact Eq.mp (by rw [C.dist_symm (x := r) (y := c2)]) raw
  have withinDoubleRadius : C.dist c1 r + C.dist c2 r <= C.radius + C.radius :=
    Nat.add_le_add nearC1 nearC2
  have belowMinimum : C.dist c1 c2 < C.minDistance :=
    Nat.lt_of_le_of_lt (Nat.le_trans triangle withinDoubleRadius) C.radius_bound
  constructor
  · exact C.min_distance_sound codeC1 codeC2 belowMinimum
  · exact ⟨C.distLedger c1 c2, C.dist_metric codeC1 codeC2⟩

end BEDC.Derived.ErrorCodeUp
