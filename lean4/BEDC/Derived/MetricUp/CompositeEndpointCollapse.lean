import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist

theorem MetricDistanceWitness_empty_distance_composite_endpoint_collapse
    {x y z dxy dyz : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      hsame dxy BHist.Empty -> hsame dyz BHist.Empty ->
        hsame x y ∧ hsame y z ∧ hsame x z := by
  intro xy yz dxyEmpty dyzEmpty
  have xyEndpoints : hsame x BHist.Empty ∧ hsame y BHist.Empty := by
    cases dxyEmpty
    exact (MetricDistanceWitness_empty_distance_iff (x := x) (y := y)).mp xy
  have yzEndpoints : hsame y BHist.Empty ∧ hsame z BHist.Empty := by
    cases dyzEmpty
    exact (MetricDistanceWitness_empty_distance_iff (x := y) (y := z)).mp yz
  exact
    And.intro (hsame_trans xyEndpoints.left (hsame_symm xyEndpoints.right))
      (And.intro (hsame_trans yzEndpoints.left (hsame_symm yzEndpoints.right))
        (hsame_trans xyEndpoints.left (hsame_symm yzEndpoints.right)))

end BEDC.Derived.MetricUp
