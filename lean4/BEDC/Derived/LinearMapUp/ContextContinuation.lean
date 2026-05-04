import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem LinearMapSingletonEval_context_continuation_append_target_carrier_iff
    {p f x y q r : BHist} :
    Cont (append p (LinearMapSingletonEval f x)) y (append q r) ->
      (LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier y ↔
        LinearMapSingletonCarrier q ∧ LinearMapSingletonCarrier r) := by
  intro continuation
  constructor
  · intro carriers
    have evalCarrier : LinearMapSingletonCarrier (LinearMapSingletonEval f x) :=
      hsame_refl BHist.Empty
    have contextCarrier : LinearMapSingletonCarrier
        (append p (LinearMapSingletonEval f x)) :=
      append_eq_empty_iff.mpr (And.intro carriers.left evalCarrier)
    have resultCarrier : LinearMapSingletonCarrier (append q r) :=
      cont_respects_hsame contextCarrier carriers.right continuation
        (cont_right_unit BHist.Empty)
    exact append_eq_empty_iff.mp resultCarrier
  · intro carriers
    have resultCarrier : LinearMapSingletonCarrier (append q r) :=
      append_eq_empty_iff.mpr carriers
    have emptyContinuation : Cont (append p (LinearMapSingletonEval f x)) y BHist.Empty :=
      cont_result_hsame_transport continuation resultCarrier
    have endpoints := cont_empty_result_inversion emptyContinuation
    have contextParts := append_eq_empty_iff.mp endpoints.left
    exact And.intro contextParts.left endpoints.right

end BEDC.Derived.LinearMapUp
