import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MatrixSingletonPow_append_positive_suffix_cont_readback {M pref suffix : BHist} :
    UnaryHistory suffix -> (hsame suffix BHist.Empty -> False) ->
      ∃ tail : BHist, UnaryHistory tail ∧
        Cont (MatrixSingletonPow M (append pref tail)) M
          (MatrixSingletonPow M (append pref suffix)) := by
  intro suffixUnary suffixNonempty
  have suffixTail := unary_history_nonempty_e1_tail suffixUnary suffixNonempty
  cases suffixTail with
  | intro tail data =>
      cases data.left
      exact ⟨tail, data.right, cont_intro rfl⟩

end BEDC.Derived.MatrixUp
