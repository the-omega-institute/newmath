import BEDC.Derived.MetricUp.DepthClassifier

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

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

theorem MetricDistanceWitness_visible_context_depth_zero_collapse {p q x y d : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p d) q) ->
      MetricDistanceDepth d = 0 ->
        hsame d BHist.Empty ∧ hsame x BHist.Empty ∧ hsame y BHist.Empty := by
  intro visible depthZero
  have visibleData :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x)
      (y := y) (d := d)).mp visible
  have endpoints := MetricDistanceWitness_depth_zero_empty_endpoints visibleData.right.right depthZero
  exact And.intro (MetricDistanceDepth_zero_iff_empty.mp depthZero) endpoints

end BEDC.Derived.MetricUp
