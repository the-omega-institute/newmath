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

theorem RegseqratStreamnameScopedInterface {s t u s' t' : BHist -> BHist} :
    RatStreamNameCarrier s ->
      RatStreamNameCarrier t ->
        RatStreamNameCarrier u ->
          RealUnaryStreamClassifier s t ->
            RealUnaryStreamClassifier t u ->
              (forall n : BHist, UnaryHistory n -> hsame (s n) (s' n)) ->
                (forall n : BHist, UnaryHistory n -> hsame (t n) (t' n)) ->
                  RatStreamNameClassifier s t ∧
                    RealUnaryStreamClassifier s s ∧
                      RealUnaryStreamClassifier t s ∧
                        RealUnaryStreamClassifier s u ∧
                          (forall n : BHist, UnaryHistory n ->
                            RatHistoryCarrier (s n) ∧ RatHistoryCarrier (t n)) ∧
                            RealUnaryStreamClassifier s' t' ∧
                              RatStreamNameClassifier s' t' := by
  intro carrierS carrierT carrierU classifiedST classifiedTU sameS sameT
  have stability :=
    RealUnaryStreamClassifier_stability_package carrierS carrierT carrierU classifiedST
      classifiedTU sameS sameT
  have transportedName :
      RatStreamNameClassifier s' t' :=
    RealUnaryStreamClassifier_streamName_transport carrierS carrierT classifiedST sameS sameT
  exact
    ⟨stability.left, stability.right.left, stability.right.right.left,
      stability.right.right.right.left, stability.right.right.right.right.left,
      stability.right.right.right.right.right, transportedName⟩

end BEDC.Derived.RealUp
