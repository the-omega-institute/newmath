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

end BEDC.Derived.TuringMachineUp
