import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
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

theorem TuringMachineStepRow_hsame_transport {current current' bound bound' next next' : BHist} :
    UnaryHistory current -> UnaryHistory bound -> Cont current bound next -> hsame current current' ->
      hsame bound bound' -> hsame next next' ->
        UnaryHistory current' ∧ UnaryHistory bound' ∧ UnaryHistory next' ∧
          Cont current' bound' next' := by
  intro currentUnary boundUnary step sameCurrent sameBound sameNext
  have currentUnary' : UnaryHistory current' := unary_transport currentUnary sameCurrent
  have boundUnary' : UnaryHistory bound' := unary_transport boundUnary sameBound
  have nextUnary : UnaryHistory next := unary_cont_closed currentUnary boundUnary step
  have nextUnary' : UnaryHistory next' := unary_transport nextUnary sameNext
  have step' : Cont current' bound' next' :=
    cont_hsame_transport sameCurrent sameBound sameNext step
  exact And.intro currentUnary'
    (And.intro boundUnary' (And.intro nextUnary' step'))

end BEDC.Derived.TuringMachineUp
