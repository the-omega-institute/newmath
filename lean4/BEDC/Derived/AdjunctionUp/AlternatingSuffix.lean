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

end BEDC.Derived.AdjunctionUp
