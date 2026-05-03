import BEDC.Derived.MetricUp
import BEDC.Derived.RealUp

namespace BEDC.Derived.CompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.MetricUp
open BEDC.Derived.RealUp
open BEDC.Derived.RatUp

theorem CompletionMetricDistanceWitness_e1_tail_real_prefix_readback
    {x y : Nat -> BHist} {n : Nat} {tail : BHist} :
    RealStreamPrefixClassifier x y n -> MetricDistanceWitness (x n) (y n) (BHist.e1 tail) ->
      UnaryHistory tail ∧ RatHistoryClassifier (x n) (y n) := by
  intro hPrefix hDistance
  exact And.intro (unary_e1_inversion hDistance.2.2.1)
    (RealStreamPrefixClassifier_endpoint n hPrefix)

end BEDC.Derived.CompletionUp
