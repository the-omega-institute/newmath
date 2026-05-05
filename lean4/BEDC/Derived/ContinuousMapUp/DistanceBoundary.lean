import BEDC.Derived.ContinuousMapUp
import BEDC.Derived.MetricUp.DepthClassifier

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.MetricUp

theorem ContinuousMapCarrier_distance_empty_iff {source map target modulus cert distance :
    BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      (hsame distance BHist.Empty ↔
        hsame source BHist.Empty ∧ hsame target BHist.Empty) := by
  intro carrier
  constructor
  · intro distanceEmpty
    cases distanceEmpty
    exact (MetricDistanceWitness_empty_distance_iff (x := source) (y := target)).mp
      carrier.right
  · intro endpoints
    have emptyDistance : MetricDistanceWitness source target BHist.Empty :=
      (MetricDistanceWitness_empty_distance_iff (x := source) (y := target)).mpr endpoints
    exact
      MetricDistanceWitness_hsame_result_deterministic
        (hsame_refl source) (hsame_refl target) carrier.right emptyDistance

theorem ContinuousMapCarrier_distance_zero_iff_empty_endpoints
    {source map target modulus cert distance : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      (MetricDistanceDepth distance = 0 ↔
        hsame source BHist.Empty ∧ hsame target BHist.Empty) := by
  intro carrier
  constructor
  · intro depthZero
    have distanceEmpty : hsame distance BHist.Empty :=
      (MetricDistanceDepth_zero_iff_empty (d := distance)).mp depthZero
    exact (ContinuousMapCarrier_distance_empty_iff carrier).mp distanceEmpty
  · intro endpoints
    have distanceEmpty : hsame distance BHist.Empty :=
      (ContinuousMapCarrier_distance_empty_iff carrier).mpr endpoints
    exact (MetricDistanceDepth_zero_iff_empty (d := distance)).mpr distanceEmpty

end BEDC.Derived.ContinuousMapUp
