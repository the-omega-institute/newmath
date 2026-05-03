import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_empty_source_e1_distance_target_exactness {target d : BHist} :
    MetricDistanceWitness BHist.Empty target (BHist.e1 d) ->
      target = BHist.e1 d /\ UnaryHistory d := by
  intro witness
  have boundary :=
    (MetricDistanceWitness_empty_left_iff (y := target) (d := BHist.e1 d)).mp witness
  have targetShape := hsame_e1_inversion boundary.right
  cases targetShape with
  | intro k data =>
      cases data with
      | intro targetEq sameDK =>
          cases sameDK
          cases targetEq
          exact And.intro rfl (unary_e1_inversion boundary.left)

end BEDC.Derived.MetricUp
