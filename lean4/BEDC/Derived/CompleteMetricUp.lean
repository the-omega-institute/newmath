import BEDC.Derived.MetricUp
import BEDC.Derived.MetricUp.Transport
import BEDC.Derived.RatUp

namespace BEDC.Derived.CompleteMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.MetricUp
open BEDC.Derived.RatUp

def CompleteMetricLimitWitness (X : BHist -> Prop) (s M : BHist -> BHist)
    (limit : BHist) : Prop :=
  X limit ∧
    forall {n : BHist}, UnaryHistory n -> X (s n) ->
      exists d : BHist,
        MetricDistanceWitness (s n) limit d ∧
          Cont (s n) limit d ∧ RatHistoryClassifier d (M n)

theorem CompleteMetricLimitWitness_hsame_transport {X : BHist -> Prop}
    {s s' M M' : BHist -> BHist} {limit limit' : BHist} :
    (forall {h k : BHist}, hsame h k -> X h -> X k) ->
      (forall {n : BHist}, UnaryHistory n -> hsame (s n) (s' n)) ->
        (forall {n : BHist}, UnaryHistory n -> hsame (M n) (M' n)) ->
          hsame limit limit' -> CompleteMetricLimitWitness X s M limit ->
            CompleteMetricLimitWitness X s' M' limit' := by
  intro carrierTransport streamTransport modulusTransport sameLimit witness
  constructor
  · exact carrierTransport sameLimit witness.left
  · intro n nUnary source
    have sourceOld : X (s n) :=
      carrierTransport (hsame_symm (streamTransport nUnary)) source
    cases witness.right nUnary sourceOld with
    | intro d distanceData =>
        exact ⟨d,
          MetricDistanceWitness_hsame_fields_transport (streamTransport nUnary) sameLimit
            (hsame_refl d) distanceData.left,
          MetricDistanceWitness_cont_hsame_transport (streamTransport nUnary) sameLimit
            (hsame_refl d) distanceData.left,
          RatHistoryClassifier_hsame_transport (hsame_refl d) (modulusTransport nUnary)
            distanceData.right.right⟩

end BEDC.Derived.CompleteMetricUp
