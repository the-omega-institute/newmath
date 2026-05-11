import BEDC.Derived.LQRUp
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.LQRUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem LQRFiniteControlPacket_empty_horizon_backward_readback [AskSetup] [PackageSetup]
    {state control transition cost horizon successorValue estimatorInput backwardUpdate
      predecessorValue endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost horizon successorValue estimatorInput
        backwardUpdate predecessorValue endpoint bundle pkg ->
      hsame horizon BHist.Empty ->
        hsame predecessorValue backwardUpdate ∧
          Cont backwardUpdate horizon predecessorValue ∧ PkgSig bundle endpoint pkg := by
  intro packet horizonEmpty
  rcases packet with
    ⟨_stateUnary, _controlUnary, _transitionUnary, _costUnary, _horizonUnary,
      _successorUnary, _estimatorUnary, _backwardUnary, _predecessorUnary, _endpointUnary,
      _stateControlRow, _transitionCostRow, _successorEstimatorRow, backwardHorizonRow,
      _predecessorCostRow, _estimatorTransitionRow, _backwardControlRow, _successorHorizonRow,
      endpointPkg⟩
  cases horizonEmpty
  exact
    ⟨cont_right_unit_result backwardHorizonRow,
      backwardHorizonRow,
      endpointPkg⟩

end BEDC.Derived.LQRUp
