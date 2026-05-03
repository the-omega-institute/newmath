import BEDC.Derived.MetricUp
import BEDC.Derived.RealUp

namespace BEDC.Derived.CompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.Cont
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

theorem CompletionMetricDistanceWitness_visible_context_e1_tail_real_prefix_readback
    {x y : Nat -> BHist} {n : Nat} {p q tail : BHist} :
    RealStreamPrefixClassifier x y n ->
      MetricDistanceWitness (append p (x n)) (append (y n) q)
        (append (append p (BHist.e1 tail)) q) ->
        UnaryHistory tail ∧ RatHistoryClassifier (x n) (y n) := by
  intro hPrefix hDistance
  have visibleBase :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x n)
      (y := y n) (d := BHist.e1 tail)).mp hDistance
  exact And.intro (unary_e1_inversion visibleBase.right.right.right.right.left)
    (RealStreamPrefixClassifier_endpoint n hPrefix)

end BEDC.Derived.CompletionUp
