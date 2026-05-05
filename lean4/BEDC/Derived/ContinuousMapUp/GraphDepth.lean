import BEDC.Derived.ContinuousMapUp

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.ContinuousUp
open BEDC.Derived.MetricUp

theorem ContinuousMapCarrier_graph_cont_depth_add {source map target modulus cert distance : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      Cont source map target ∧
        MetricDistanceDepth target = MetricDistanceDepth source + MetricDistanceDepth map := by
  intro carrier
  have graphRel : Cont source map target := carrier.left.right.right.right.right.left
  have graphWitness : MetricDistanceWitness source map target :=
    And.intro carrier.left.left
      (And.intro carrier.left.right.right.left (And.intro carrier.left.right.left graphRel))
  exact And.intro graphRel (MetricDistanceWitness_depth_add graphWitness)

end BEDC.Derived.ContinuousMapUp
