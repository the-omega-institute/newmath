import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.RecursiveFnUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem RecursiveFnCompositionPrimitiveRecursion_obligation_surface
    {constructorHistory input innerTrace outerTrace baseStep seqTrace finalGraph : BHist} :
    UnaryHistory constructorHistory -> UnaryHistory input -> UnaryHistory baseStep ->
      Cont constructorHistory input innerTrace -> Cont innerTrace baseStep outerTrace ->
        Cont constructorHistory baseStep seqTrace -> Cont outerTrace seqTrace finalGraph ->
          ∃ repackedInput repackedGraph : BHist,
            Cont input baseStep repackedInput ∧ Cont constructorHistory repackedInput repackedGraph ∧
              UnaryHistory innerTrace ∧ UnaryHistory outerTrace ∧ UnaryHistory seqTrace ∧
                UnaryHistory finalGraph ∧ UnaryHistory repackedInput ∧ UnaryHistory repackedGraph ∧
                  hsame outerTrace repackedGraph ∧ hsame finalGraph (append outerTrace seqTrace) := by
  intro constructorUnary inputUnary baseStepUnary innerTraceRow outerTraceRow seqTraceRow
  intro finalGraphRow
  have innerTraceUnary : UnaryHistory innerTrace :=
    unary_cont_closed constructorUnary inputUnary innerTraceRow
  have outerTraceUnary : UnaryHistory outerTrace :=
    unary_cont_closed innerTraceUnary baseStepUnary outerTraceRow
  have seqTraceUnary : UnaryHistory seqTrace :=
    unary_cont_closed constructorUnary baseStepUnary seqTraceRow
  have finalGraphUnary : UnaryHistory finalGraph :=
    unary_cont_closed outerTraceUnary seqTraceUnary finalGraphRow
  cases cont_assoc_left_exists innerTraceRow outerTraceRow with
  | intro repackedInput repackedRows =>
      have repackedInputUnary : UnaryHistory repackedInput :=
        unary_cont_closed inputUnary baseStepUnary repackedRows.left
      have repackedGraphUnary : UnaryHistory outerTrace :=
        unary_cont_closed constructorUnary repackedInputUnary repackedRows.right
      have outerTraceSame : hsame outerTrace outerTrace :=
        hsame_refl outerTrace
      exact
        ⟨repackedInput, outerTrace, repackedRows.left, repackedRows.right, innerTraceUnary,
          outerTraceUnary, seqTraceUnary, finalGraphUnary, repackedInputUnary, repackedGraphUnary,
          outerTraceSame, finalGraphRow⟩

end BEDC.Derived.RecursiveFnUp
