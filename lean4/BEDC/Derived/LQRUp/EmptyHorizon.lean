import BEDC.Derived.LQRUp
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.LQRUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LQRFiniteControlPacket_empty_horizon_backward_ledger [AskSetup] [PackageSetup]
    {state control transition cost successorValue estimatorInput backwardUpdate predecessorValue
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost BHist.Empty successorValue estimatorInput
        backwardUpdate predecessorValue endpoint bundle pkg ->
      Cont backwardUpdate BHist.Empty predecessorValue ∧
        hsame predecessorValue backwardUpdate ∧
          UnaryHistory backwardUpdate ∧ PkgSig bundle endpoint pkg := by
  intro packet
  obtain ⟨_stateUnary, _controlUnary, _transitionUnary, _costUnary, _horizonUnary,
    _successorUnary, _estimatorUnary, backwardUnary, _predecessorUnary, _endpointUnary,
    _stateControlRow, _transitionCostRow, _successorEstimatorRow, backwardHorizonRow,
    _predecessorCostRow, _estimatorTransitionRow, _backwardControlRow, _successorHorizonRow,
    pkgSig⟩ := packet
  exact And.intro backwardHorizonRow
    (And.intro (cont_right_unit_result backwardHorizonRow) (And.intro backwardUnary pkgSig))

theorem LQRFiniteControlPacket_empty_horizon_predecessor_update_hsame [AskSetup] [PackageSetup]
    {state control transition cost horizon successorValue estimatorInput backwardUpdate
      predecessorValue endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost horizon successorValue estimatorInput
        backwardUpdate predecessorValue endpoint bundle pkg ->
      hsame horizon BHist.Empty ->
        hsame predecessorValue backwardUpdate ∧
          Cont backwardUpdate horizon predecessorValue ∧ PkgSig bundle endpoint pkg := by
  intro packet sameHorizonEmpty
  rcases packet with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, backwardHorizonRow, _, _, _, _, packageRow⟩
  have emptyHorizonRow : Cont backwardUpdate BHist.Empty predecessorValue := by
    cases sameHorizonEmpty
    exact backwardHorizonRow
  have samePredecessorBackward : hsame predecessorValue backwardUpdate :=
    cont_right_unit_iff.mp emptyHorizonRow
  exact And.intro samePredecessorBackward (And.intro backwardHorizonRow packageRow)

end BEDC.Derived.LQRUp
