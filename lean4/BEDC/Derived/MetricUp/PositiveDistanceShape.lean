import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_positive_distance_e1_shape {x y d : BHist} :
    MetricDistanceWitness x y d -> (MetricDistanceDepth d = 0 -> False) ->
      ∃ tail : BHist, d = BHist.e1 tail ∧ UnaryHistory tail := by
  intro witness positiveDepth
  have dCarrier : UnaryHistory d := witness.2.2.1
  cases d with
  | Empty =>
      exact False.elim (positiveDepth rfl)
  | e0 d0 =>
      cases dCarrier
  | e1 tail =>
      exact Exists.intro tail (And.intro rfl (unary_e1_inversion dCarrier))

end BEDC.Derived.MetricUp
