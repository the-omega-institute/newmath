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

theorem RecursiveFnZeroSuccessorProjection_obligation_surface
    {constructor input zeroOutput successorOutput projectionOutput baseSurface : BHist} :
    UnaryHistory constructor -> UnaryHistory input -> UnaryHistory zeroOutput ->
      Cont constructor zeroOutput successorOutput -> Cont input zeroOutput projectionOutput ->
        Cont successorOutput projectionOutput baseSurface ->
          UnaryHistory successorOutput ∧ UnaryHistory projectionOutput ∧ UnaryHistory baseSurface ∧
            hsame successorOutput (append constructor zeroOutput) ∧
              hsame projectionOutput (append input zeroOutput) ∧
                hsame baseSurface (append successorOutput projectionOutput) := by
  intro constructorUnary inputUnary zeroOutputUnary successorRow projectionRow baseSurfaceRow
  have successorUnary : UnaryHistory successorOutput :=
    unary_cont_closed constructorUnary zeroOutputUnary successorRow
  have projectionUnary : UnaryHistory projectionOutput :=
    unary_cont_closed inputUnary zeroOutputUnary projectionRow
  have baseSurfaceUnary : UnaryHistory baseSurface :=
    unary_cont_closed successorUnary projectionUnary baseSurfaceRow
  exact
    ⟨successorUnary, projectionUnary, baseSurfaceUnary, successorRow, projectionRow,
      baseSurfaceRow⟩

theorem RecursiveFnBoundedMinimisationLedger_exactness
    {constructor bound testedTrace witness output ledger : BHist} {failureTail : BHist} :
    UnaryHistory constructor -> UnaryHistory bound -> UnaryHistory witness ->
      Cont constructor bound testedTrace -> Cont testedTrace witness output ->
        Cont bound output ledger -> hsame witness (BHist.e1 failureTail) ->
          UnaryHistory testedTrace ∧ UnaryHistory output ∧ UnaryHistory ledger ∧
            hsame testedTrace (append constructor bound) ∧ hsame output (append testedTrace witness) ∧
              hsame ledger (append bound output) ∧ (hsame witness BHist.Empty -> False) := by
  intro constructorUnary boundUnary witnessUnary testedTraceRow outputRow ledgerRow witnessFailure
  have testedTraceUnary : UnaryHistory testedTrace :=
    unary_cont_closed constructorUnary boundUnary testedTraceRow
  have outputUnary : UnaryHistory output :=
    unary_cont_closed testedTraceUnary witnessUnary outputRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed boundUnary outputUnary ledgerRow
  have witnessNonempty : hsame witness BHist.Empty -> False := by
    intro witnessEmpty
    exact not_hsame_e1_empty (witnessFailure.symm.trans witnessEmpty)
  exact
    ⟨testedTraceUnary, outputUnary, ledgerUnary, testedTraceRow, outputRow, ledgerRow,
      witnessNonempty⟩

end BEDC.Derived.RecursiveFnUp
