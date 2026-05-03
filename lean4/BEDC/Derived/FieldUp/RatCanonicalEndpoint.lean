import BEDC.Derived.RatUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_canonical_right_unit_endpoint_empty {u : BHist} :
    (forall {r : BHist}, Cont (BHist.e1 BHist.Empty) u r ->
      RatHistoryClassifier r (BHist.e1 BHist.Empty)) -> hsame u BHist.Empty := by
  intro rightUnit
  have canonicalContinuation : Cont (BHist.e1 BHist.Empty) u (append (BHist.e1 BHist.Empty) u) :=
    cont_intro rfl
  have classifiedResult :
      RatHistoryClassifier (append (BHist.e1 BHist.Empty) u) (BHist.e1 BHist.Empty) :=
    rightUnit canonicalContinuation
  have collapsedContinuation : Cont (BHist.e1 BHist.Empty) u (BHist.e1 BHist.Empty) :=
    cont_result_hsame_transport canonicalContinuation classifiedResult.right.right
  exact cont_right_unit_unique collapsedContinuation

theorem field_rat_denominator_canonical_left_unit_endpoint_empty {u : BHist} :
    (forall {r : BHist}, Cont u (BHist.e1 BHist.Empty) r ->
      RatHistoryClassifier r (BHist.e1 BHist.Empty)) -> hsame u BHist.Empty := by
  intro leftUnit
  have canonicalContinuation : Cont u (BHist.e1 BHist.Empty) (append u (BHist.e1 BHist.Empty)) :=
    cont_intro rfl
  have classifiedResult :
      RatHistoryClassifier (append u (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty) :=
    leftUnit canonicalContinuation
  have collapsedContinuation : Cont u (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    cont_result_hsame_transport canonicalContinuation classifiedResult.right.right
  exact cont_left_unit_unique collapsedContinuation

theorem field_rat_denominator_e1_probe_classifier_endpoint_empty {u : BHist} :
    RatHistoryClassifier (append u (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty) ->
      hsame u BHist.Empty := by
  intro classified
  exact cont_left_unit_unique (cont_result_hsame_transport (cont_intro rfl) classified.right.right)

theorem field_rat_denominator_right_e1_probe_classifier_endpoint_empty {u : BHist} :
    RatHistoryClassifier (append (BHist.e1 BHist.Empty) u) (BHist.e1 BHist.Empty) ->
      hsame u BHist.Empty := by
  intro classified
  exact cont_right_unit_unique
    (cont_result_hsame_transport (cont_intro rfl) classified.right.right)

end BEDC.Derived.FieldUp
