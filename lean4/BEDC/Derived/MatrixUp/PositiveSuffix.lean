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

theorem MatrixSingletonPow_append_positive_suffix_classifier_readback {M pref suffix : BHist} :
    MatrixSingletonCarrier M -> UnaryHistory pref -> UnaryHistory suffix ->
      (hsame suffix BHist.Empty -> False) ->
        exists tail : BHist, UnaryHistory tail ∧
          MatrixSingletonClassifier (MatrixSingletonPow M (append pref suffix))
            (MatrixSingletonMul (MatrixSingletonPow M (append pref tail)) M) := by
  intro carrierM unaryPref unarySuffix suffixNonempty
  have readback :=
    MatrixSingletonPow_append_positive_suffix_cont_readback (M := M) (pref := pref)
      unarySuffix suffixNonempty
  cases readback with
  | intro tail data =>
      have compositeCarrier : MatrixSingletonCarrier (MatrixSingletonPow M (append pref suffix)) :=
        MatrixSingletonPow_carrier_closed carrierM (unary_append_closed unaryPref unarySuffix)
      have prefixTailUnary : UnaryHistory (append pref tail) :=
        unary_append_closed unaryPref data.left
      have predecessorCarrier : MatrixSingletonCarrier (MatrixSingletonPow M (append pref tail)) :=
        MatrixSingletonPow_carrier_closed carrierM prefixTailUnary
      have productCarrier :
          MatrixSingletonCarrier
            (MatrixSingletonMul (MatrixSingletonPow M (append pref tail)) M) :=
        append_eq_empty_iff.mpr (And.intro predecessorCarrier carrierM)
      have sameResult :
          hsame (MatrixSingletonPow M (append pref suffix))
            (MatrixSingletonMul (MatrixSingletonPow M (append pref tail)) M) := by
        exact data.right
      exact Exists.intro tail
        (And.intro data.left
          (And.intro compositeCarrier (And.intro productCarrier sameResult)))

end BEDC.Derived.MatrixUp
