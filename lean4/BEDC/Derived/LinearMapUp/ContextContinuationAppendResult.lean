import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem LinearMapSingletonEval_context_continuation_append_result_carrier_iff
    {p f x y q r : BHist} :
    LinearMapSingletonCarrier p ->
      Cont (append p (LinearMapSingletonEval f x)) y (append q r) ->
        (LinearMapSingletonCarrier y ↔
          LinearMapSingletonCarrier q ∧ LinearMapSingletonCarrier r) := by
  intro carrierP continuation
  constructor
  · intro carrierY
    have evalCarrier : LinearMapSingletonCarrier (LinearMapSingletonEval f x) :=
      hsame_refl BHist.Empty
    have contextCarrier : LinearMapSingletonCarrier (append p (LinearMapSingletonEval f x)) :=
      append_eq_empty_iff.mpr (And.intro carrierP evalCarrier)
    have resultCarrier : LinearMapSingletonCarrier (append q r) :=
      cont_respects_hsame contextCarrier carrierY continuation (cont_right_unit BHist.Empty)
    exact append_eq_empty_iff.mp resultCarrier
  · intro carriers
    have resultCarrier : LinearMapSingletonCarrier (append q r) :=
      append_eq_empty_iff.mpr carriers
    have emptyContinuation :
        Cont (append p (LinearMapSingletonEval f x)) y BHist.Empty :=
      cont_result_hsame_transport continuation resultCarrier
    exact (cont_empty_result_inversion emptyContinuation).right

theorem LinearMapSingletonClassifier_continuation_append_source_append_result_iff
    {p q r s t h : BHist} :
    Cont (append p q) r (append s t) ->
      (LinearMapSingletonClassifier (append s t) h <->
        LinearMapSingletonCarrier p /\ LinearMapSingletonCarrier q /\
          LinearMapSingletonCarrier r /\ LinearMapSingletonCarrier s /\
            LinearMapSingletonCarrier t /\ LinearMapSingletonCarrier h) := by
  intro continuation
  constructor
  · intro classified
    have sourceData :=
      (LinearMapSingletonClassifier_continuation_append_source_classifier_iff
        (p := p) (q := q) (r := r) (h := append s t) (t := h) continuation).mp
        classified
    have resultParts := append_eq_empty_iff.mp classified.left
    exact And.intro sourceData.left
      (And.intro sourceData.right.left
        (And.intro sourceData.right.right.left
          (And.intro resultParts.left
            (And.intro resultParts.right sourceData.right.right.right))))
  · intro carriers
    exact
      (LinearMapSingletonClassifier_continuation_append_source_classifier_iff
        (p := p) (q := q) (r := r) (h := append s t) (t := h) continuation).mpr
        (And.intro carriers.left
          (And.intro carriers.right.left
            (And.intro carriers.right.right.left carriers.right.right.right.right.right)))

end BEDC.Derived.LinearMapUp
