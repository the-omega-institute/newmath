import BEDC.Derived.MetricUp

namespace BEDC.Derived.ErrorCodeUp

open BEDC.FKernel.Hist
open BEDC.Derived.MetricUp

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
