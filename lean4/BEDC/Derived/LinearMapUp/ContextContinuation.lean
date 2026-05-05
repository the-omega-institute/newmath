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

theorem LinearMapSingletonEval_context_append_input_result_carrier_iff
    {p f x y z q r : BHist} :
    Cont (append p (LinearMapSingletonEval f x)) (append y z) (append q r) ->
      (LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier y ∧
          LinearMapSingletonCarrier z ↔
        LinearMapSingletonCarrier q ∧ LinearMapSingletonCarrier r) := by
  intro continuation
  have base :=
    LinearMapSingletonEval_context_continuation_append_target_carrier_iff
      (p := p) (f := f) (x := x) (y := append y z) (q := q) (r := r) continuation
  constructor
  · intro carriers
    have inputCarrier : LinearMapSingletonCarrier (append y z) :=
      append_eq_empty_iff.mpr (And.intro carriers.right.left carriers.right.right)
    exact base.mp (And.intro carriers.left inputCarrier)
  · intro carriers
    have contextCarriers := base.mpr carriers
    have inputParts := append_eq_empty_iff.mp contextCarriers.right
    exact And.intro contextCarriers.left (And.intro inputParts.left inputParts.right)

end BEDC.Derived.LinearMapUp
