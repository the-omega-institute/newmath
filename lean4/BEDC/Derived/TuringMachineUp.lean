import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.TuringMachineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem TuringMachineConfigurationTraceCarrier_configuration_trace_surface
    {state tape head bound configuration trace endpoint : BHist} :
    UnaryHistory state -> UnaryHistory tape -> UnaryHistory head -> UnaryHistory bound ->
      Cont state tape configuration -> Cont configuration head trace ->
        Cont trace bound endpoint ->
          UnaryHistory configuration ∧ UnaryHistory trace ∧ UnaryHistory endpoint ∧
            hsame configuration (append state tape) ∧ hsame trace (append configuration head) ∧
              hsame endpoint (append trace bound) := by
  intro stateUnary tapeUnary headUnary boundUnary configurationRow traceRow endpointRow
  have configurationUnary : UnaryHistory configuration :=
    unary_cont_closed stateUnary tapeUnary configurationRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed configurationUnary headUnary traceRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed traceUnary boundUnary endpointRow
  exact
    ⟨configurationUnary, traceUnary, endpointUnary, configurationRow, traceRow, endpointRow⟩

theorem TuringMachineDeterministicStepTransport_step_stability
    {current table next current' table' next' trace extended : BHist} :
    UnaryHistory current -> UnaryHistory table -> UnaryHistory trace -> Cont current table next ->
      hsame current current' -> hsame table table' -> Cont current' table' next' ->
        Cont trace next' extended ->
          UnaryHistory next ∧ UnaryHistory next' ∧ hsame next next' ∧
            hsame extended (append trace next') := by
  intro currentUnary tableUnary traceUnary stepRow sameCurrent sameTable stepRow' traceRow
  have nextUnary : UnaryHistory next :=
    unary_cont_closed currentUnary tableUnary stepRow
  have currentUnary' : UnaryHistory current' :=
    unary_transport currentUnary sameCurrent
  have tableUnary' : UnaryHistory table' :=
    unary_transport tableUnary sameTable
  have nextUnary' : UnaryHistory next' :=
    unary_cont_closed currentUnary' tableUnary' stepRow'
  have sameNext : hsame next next' :=
    cont_respects_hsame sameCurrent sameTable stepRow stepRow'
  exact ⟨nextUnary, nextUnary', sameNext, traceRow⟩

theorem TuringMachineFiniteTapeReadbackCarrier_finite_readback_surface
    {tape head readback trace bounded : BHist} :
    UnaryHistory tape -> UnaryHistory head -> UnaryHistory trace -> Cont tape head readback ->
      Cont trace readback bounded ->
        UnaryHistory readback ∧ UnaryHistory bounded ∧ hsame readback (append tape head) ∧
          hsame bounded (append trace readback) := by
  intro tapeUnary headUnary traceUnary readbackRow boundedRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed tapeUnary headUnary readbackRow
  have boundedUnary : UnaryHistory bounded :=
    unary_cont_closed traceUnary readbackUnary boundedRow
  exact ⟨readbackUnary, boundedUnary, readbackRow, boundedRow⟩

end BEDC.Derived.TuringMachineUp
