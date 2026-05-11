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

end BEDC.Derived.LQRUp
