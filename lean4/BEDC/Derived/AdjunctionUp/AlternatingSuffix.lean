import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem AdjunctionUnitCounitAlternating_append_positive_suffix_cont_readback
    {unit counit pref suffix : BHist} :
    UnaryHistory suffix -> (hsame suffix BHist.Empty -> False) ->
      ∃ tail : BHist, UnaryHistory tail ∧
        Cont unit (AdjunctionUnitCounitAlternating counit unit (append pref tail))
          (AdjunctionUnitCounitAlternating unit counit (append pref suffix)) := by
  intro suffixUnary suffixNonempty
  have suffixTail := unary_history_nonempty_e1_tail suffixUnary suffixNonempty
  cases suffixTail with
  | intro tail data =>
      cases data.left
      exact ⟨tail, data.right, cont_intro rfl⟩

theorem AdjunctionUnitCounitAlternating_append_positive_suffix_result_empty_unit_empty
    {unit counit pref suffix : BHist} :
    UnaryHistory suffix -> (hsame suffix BHist.Empty -> False) ->
      hsame (AdjunctionUnitCounitAlternating unit counit (append pref suffix)) BHist.Empty ->
        hsame unit BHist.Empty := by
  intro suffixUnary suffixNonempty resultEmpty
  have readback :=
    AdjunctionUnitCounitAlternating_append_positive_suffix_cont_readback
      (unit := unit) (counit := counit) (pref := pref)
      suffixUnary suffixNonempty
  cases readback with
  | intro tail data =>
      have emptyContinuation : Cont unit
          (AdjunctionUnitCounitAlternating counit unit (append pref tail)) BHist.Empty :=
        cont_result_hsame_transport data.right resultEmpty
      exact (cont_empty_result_inversion emptyContinuation).left

end BEDC.Derived.AdjunctionUp
