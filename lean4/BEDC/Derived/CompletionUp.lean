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

theorem CompletionMetricDistanceWitness_e1_result_tail_deterministic
    {x y : Nat -> BHist} {n : Nat} {d e : BHist} :
    RealStreamPrefixClassifier x y n -> MetricDistanceWitness (x n) (y n) (BHist.e1 d) ->
      MetricDistanceWitness (x n) (y n) (BHist.e1 e) ->
        UnaryHistory d ∧ UnaryHistory e ∧ hsame d e ∧ RatHistoryClassifier (x n) (y n) := by
  intro hPrefix hDistanceD hDistanceE
  have dData :=
    CompletionMetricDistanceWitness_e1_tail_real_prefix_readback hPrefix hDistanceD
  have eData :=
    CompletionMetricDistanceWitness_e1_tail_real_prefix_readback hPrefix hDistanceE
  have sameDistance :
      hsame (BHist.e1 d) (BHist.e1 e) :=
    MetricDistanceWitness_hsame_result_deterministic
      (hsame_refl (x n)) (hsame_refl (y n)) hDistanceD hDistanceE
  exact And.intro dData.left
    (And.intro eData.left (And.intro (hsame_e1_iff.mp sameDistance) dData.right))

theorem CompletionMetricDistanceWitness_e1_symmetric_tail_real_prefix_readback
    {x y : Nat -> BHist} {n : Nat} {d e : BHist} :
    RealStreamPrefixClassifier x y n -> MetricDistanceWitness (x n) (y n) (BHist.e1 d) ->
      MetricDistanceWitness (y n) (x n) (BHist.e1 e) ->
        UnaryHistory d ∧ UnaryHistory e ∧ hsame d e ∧ RatHistoryClassifier (y n) (x n) := by
  intro hPrefix hDistanceD hDistanceE
  have hPrefixSymm : RealStreamPrefixClassifier y x n :=
    RealStreamPrefixClassifier_symm n hPrefix
  have dData :=
    CompletionMetricDistanceWitness_e1_tail_real_prefix_readback hPrefix hDistanceD
  have eData :=
    CompletionMetricDistanceWitness_e1_tail_real_prefix_readback hPrefixSymm hDistanceE
  have sameDistance :
      hsame (BHist.e1 d) (BHist.e1 e) :=
    MetricDistanceWitness_symmetric_classifier hDistanceD hDistanceE
  exact And.intro dData.left
    (And.intro eData.left (And.intro (hsame_e1_iff.mp sameDistance) eData.right))

end BEDC.Derived.CompletionUp
