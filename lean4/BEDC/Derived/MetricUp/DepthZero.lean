import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist

theorem MetricDistanceWitness_depth_zero_empty_endpoints {x y d : BHist} :
    MetricDistanceWitness x y d -> MetricDistanceDepth d = 0 ->
      hsame x BHist.Empty ∧ hsame y BHist.Empty := by
  intro witness depthZero
  cases d with
  | Empty =>
      exact MetricDistanceWitness_empty_distance_iff.mp witness
  | e0 d0 =>
      cases depthZero
  | e1 d1 =>
      cases depthZero

theorem MetricDistanceWitness_empty_endpoints_depth_zero {x y d : BHist} :
    MetricDistanceWitness x y d -> hsame x BHist.Empty -> hsame y BHist.Empty ->
      MetricDistanceDepth d = 0 := by
  intro witness sameX sameY
  cases sameX
  cases sameY
  cases witness.2.2.2
  rfl

end BEDC.Derived.MetricUp
