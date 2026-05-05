import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

theorem RealUnaryStreamClassifier_streamName_transport {s t s' t' : BHist -> BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t -> RealUnaryStreamClassifier s t ->
      (forall n : BHist, UnaryHistory n -> hsame (s n) (s' n)) ->
        (forall n : BHist, UnaryHistory n -> hsame (t n) (t' n)) ->
          RatStreamNameClassifier s' t' := by
  intro carrierS carrierT classified sameS sameT
  have carrierS' : RatStreamNameCarrier s' := by
    intro n nUnary
    exact RatHistoryCarrier_hsame_transport (sameS n nUnary) (carrierS n nUnary)
  have carrierT' : RatStreamNameCarrier t' := by
    intro n nUnary
    exact RatHistoryCarrier_hsame_transport (sameT n nUnary) (carrierT n nUnary)
  exact And.intro carrierS'
    (And.intro carrierT'
      (fun n nUnary =>
        RatHistoryClassifier_hsame_transport (sameS n nUnary) (sameT n nUnary)
          (classified n nUnary)))

theorem RealUnaryStreamClassifier_ratStreamName_pointwise_iff {s t : BHist -> BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t ->
      (RealUnaryStreamClassifier s t ↔
        (RatStreamNameCarrier s ∧ RatStreamNameCarrier t ∧
          forall n : BHist, UnaryHistory n -> RatHistoryClassifier (s n) (t n))) := by
  intro carrierS carrierT
  constructor
  · intro classified
    exact And.intro carrierS (And.intro carrierT classified)
  · intro classified
    exact classified.right.right

end BEDC.Derived.RealUp
