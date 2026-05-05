import BEDC.FKernel.Unary
import BEDC.FKernel.Cont
import BEDC.Derived.VecSpaceUp
import BEDC.Derived.MetricUp

namespace BEDC.Derived.ErrorCodeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.Cont
open BEDC.Derived.MetricUp
open BEDC.Derived.VecSpaceUp

def ErrorCodeMetricCodeword (c : BHist) : Prop :=
  VecSpaceSingletonCarrier c ∧ MetricDistanceWitness c BHist.Empty BHist.Empty

def ErrorCodeMetricReceivedWithinZero (c r : BHist) : Prop :=
  ErrorCodeMetricCodeword c ∧ MetricDistanceWitness c r BHist.Empty

theorem ErrorCodeMetricReceivedWithinZero_unique_decoding_empty {c1 c2 r : BHist} :
    ErrorCodeMetricReceivedWithinZero c1 r ->
      ErrorCodeMetricReceivedWithinZero c2 r ->
        hsame c1 BHist.Empty ∧ hsame c2 BHist.Empty ∧ VecSpaceSingletonClassifier c1 c2 := by
  intro first second
  have firstEndpoints :
      hsame c1 BHist.Empty ∧ hsame r BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := c1) (y := r)).mp first.right
  have secondEndpoints :
      hsame c2 BHist.Empty ∧ hsame r BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := c2) (y := r)).mp second.right
  have sameCodewords : hsame c1 c2 :=
    hsame_trans firstEndpoints.left (hsame_symm secondEndpoints.left)
  exact And.intro firstEndpoints.left
    (And.intro secondEndpoints.left
      (And.intro first.left.left (And.intro second.left.left sameCodewords)))

structure ErrorCodeMinimumDistanceDecoding where
  Code : BHist -> Prop
  rho : BHist -> BHist -> Prop
  delta : BHist -> BHist -> Nat
  d : Nat
  t : Nat
  d_pos : 0 < d
  radius_bound : t + t < d
  code_unary : forall {x : BHist}, Code x -> UnaryHistory x
  delta_symm : forall {x y : BHist}, delta x y = delta y x
  delta_triangle : forall {x y z : BHist}, delta x z <= delta x y + delta y z
  minimum_distance : forall {x y : BHist}, Code x -> Code y -> delta x y < d -> rho x y

theorem ErrorCodeMinimumDistanceDecoding_unique_decoding_radius
    (C : ErrorCodeMinimumDistanceDecoding)
    {c1 c2 r : BHist} :
    C.Code c1 -> C.Code c2 -> C.delta c1 r <= C.t -> C.delta c2 r <= C.t ->
      C.rho c1 c2 ∧ UnaryHistory c1 ∧ UnaryHistory c2 := by
  intro codeC1 codeC2 c1Near c2Near
  have belowDistance : C.delta c1 c2 < C.d := by
    calc
      C.delta c1 c2 <= C.delta c1 r + C.delta r c2 := C.delta_triangle
      _ = C.delta c1 r + C.delta c2 r :=
        congrArg (fun h => C.delta c1 r + h) (C.delta_symm (x := r) (y := c2))
      _ <= C.t + C.t := Nat.add_le_add c1Near c2Near
      _ < C.d := C.radius_bound
  exact And.intro (C.minimum_distance codeC1 codeC2 belowDistance)
    (And.intro (C.code_unary codeC1) (C.code_unary codeC2))

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
  code : BHist -> Prop
  classifier : BHist -> BHist -> Prop
  distance : BHist -> BHist -> Nat
  Code : BHist -> Prop
  rho : BHist -> BHist -> Prop
  dist : BHist -> BHist -> Nat
  distLedger : BHist -> BHist -> BHist
  minimumDistance : Nat
  decodingRadius : Nat
  minDistance : Nat
  radius : Nat
  minDistance_pos : 0 < minDistance
  distance_symm : ∀ x y : BHist, distance x y = distance y x
  distance_triangle :
    ∀ x y z : BHist, distance x z <= distance x y + distance y z
  radius_double_lt_minimum : decodingRadius + decodingRadius < minimumDistance
  radius_bound : radius + radius < minDistance
  dist_symm : forall {x y : BHist}, dist x y = dist y x
  dist_triangle : forall {x y z : BHist}, dist x z <= dist x y + dist y z
  dist_metric : forall {x y : BHist}, Code x -> Code y ->
    MetricDistanceWitness x y (distLedger x y)
  minimum_distance_classifier :
    ∀ {x y : BHist}, code x -> code y -> distance x y < minimumDistance -> classifier x y
  classifier_sound :
    ∀ {x y : BHist}, classifier x y -> hsame (append x BHist.Empty) y
  min_distance_sound : forall {x y : BHist}, Code x -> Code y ->
    dist x y < minDistance -> rho x y

theorem ErrorCodeMinimumDistanceInterface_unique_decoding_radius
    (C : ErrorCodeMinimumDistanceInterface) {c1 c2 r : BHist} :
    C.code c1 -> C.code c2 -> C.distance c1 r <= C.decodingRadius ->
      C.distance c2 r <= C.decodingRadius ->
        C.classifier c1 c2 ∧ hsame (append c1 BHist.Empty) c2 := by
  intro c1Code c2Code c1Radius c2Radius
  have rToC2Radius : C.distance r c2 <= C.decodingRadius := by
    rw [C.distance_symm r c2]
    exact c2Radius
  have combinedRadius :
      C.distance c1 r + C.distance r c2 <= C.decodingRadius + C.decodingRadius :=
    Nat.add_le_add c1Radius rToC2Radius
  have distanceBound : C.distance c1 c2 <= C.decodingRadius + C.decodingRadius :=
    Nat.le_trans (C.distance_triangle c1 r c2) combinedRadius
  have belowMinimum : C.distance c1 c2 < C.minimumDistance :=
    Nat.lt_of_le_of_lt distanceBound C.radius_double_lt_minimum
  have classified : C.classifier c1 c2 :=
    C.minimum_distance_classifier c1Code c2Code belowMinimum
  exact And.intro classified (C.classifier_sound classified)

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
