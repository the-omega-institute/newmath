import BEDC.Derived.RatUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

def RatStreamNameCarrier (s : BHist -> BHist) : Prop :=
  forall n : BHist, UnaryHistory n -> RatHistoryCarrier (s n)

def RatStreamNameClassifier (s t : BHist -> BHist) : Prop :=
  RatStreamNameCarrier s ∧ RatStreamNameCarrier t ∧
    forall n : BHist, UnaryHistory n -> RatHistoryClassifier (s n) (t n)

theorem RatStreamName_certificate_fields {s t u s' t' : BHist -> BHist} :
    RatStreamNameCarrier s ->
      RatStreamNameClassifier s t ->
        RatStreamNameClassifier t u ->
          (forall n : BHist, UnaryHistory n -> hsame (s n) (s' n)) ->
            (forall n : BHist, UnaryHistory n -> hsame (t n) (t' n)) ->
              RatStreamNameClassifier s s ∧
                RatStreamNameClassifier t s ∧
                  RatStreamNameClassifier s u ∧
                    (forall n : BHist, UnaryHistory n ->
                      RatHistoryCarrier (s n) ∧ RatHistoryCarrier (t n)) ∧
                      RatStreamNameClassifier s' t' := by
  intro carrierS classifiedST classifiedTU sameSS' sameTT'
  have carrierT : RatStreamNameCarrier t := classifiedST.right.left
  have carrierU : RatStreamNameCarrier u := classifiedTU.right.left
  have selfS : RatStreamNameClassifier s s := by
    exact And.intro carrierS
      (And.intro carrierS
        (fun n nUnary => And.intro (carrierS n nUnary)
          (And.intro (carrierS n nUnary) (hsame_refl (s n)))))
  have symmTS : RatStreamNameClassifier t s := by
    exact And.intro carrierT
      (And.intro carrierS
        (fun n nUnary => RatHistoryClassifier_symm (classifiedST.right.right n nUnary)))
  have transSU : RatStreamNameClassifier s u := by
    exact And.intro carrierS
      (And.intro carrierU
        (fun n nUnary =>
          RatHistoryClassifier_trans (classifiedST.right.right n nUnary)
            (classifiedTU.right.right n nUnary)))
  have endpointCarriers :
      forall n : BHist, UnaryHistory n -> RatHistoryCarrier (s n) ∧ RatHistoryCarrier (t n) := by
    intro n nUnary
    have point := classifiedST.right.right n nUnary
    exact And.intro point.left point.right.left
  have carrierS' : RatStreamNameCarrier s' := by
    intro n nUnary
    exact RatHistoryCarrier_hsame_transport (sameSS' n nUnary) (carrierS n nUnary)
  have carrierT' : RatStreamNameCarrier t' := by
    intro n nUnary
    exact RatHistoryCarrier_hsame_transport (sameTT' n nUnary) (carrierT n nUnary)
  have transportS'T' : RatStreamNameClassifier s' t' := by
    exact And.intro carrierS'
      (And.intro carrierT'
        (fun n nUnary =>
          RatHistoryClassifier_hsame_transport (sameSS' n nUnary) (sameTT' n nUnary)
            (classifiedST.right.right n nUnary)))
  exact And.intro selfS
    (And.intro symmTS
      (And.intro transSU
        (And.intro endpointCarriers transportS'T')))

theorem RatStreamName_reindexing_composition_law {s t : BHist -> BHist}
    {r q : BHist -> BHist}
    (r_unary : forall n : BHist, UnaryHistory n -> UnaryHistory (r n))
    (q_unary : forall n : BHist, UnaryHistory n -> UnaryHistory (q n)) :
    (forall n : BHist, UnaryHistory n -> UnaryHistory (q (r n))) ∧
      (RatStreamNameCarrier s -> RatStreamNameCarrier (fun n => s (q (r n)))) ∧
        (RatStreamNameClassifier s t ->
          RatStreamNameClassifier (fun n => s (q (r n))) (fun n => t (q (r n)))) := by
  have compositeUnary : forall n : BHist, UnaryHistory n -> UnaryHistory (q (r n)) := by
    intro n nUnary
    exact q_unary (r n) (r_unary n nUnary)
  constructor
  · exact compositeUnary
  · constructor
    · intro carrierS n nUnary
      exact carrierS (q (r n)) (compositeUnary n nUnary)
    · intro classified
      constructor
      · intro n nUnary
        exact classified.left (q (r n)) (compositeUnary n nUnary)
      · constructor
        · intro n nUnary
          exact classified.right.left (q (r n)) (compositeUnary n nUnary)
        · intro n nUnary
          exact classified.right.right (q (r n)) (compositeUnary n nUnary)

end BEDC.Derived.StreamNameUp
