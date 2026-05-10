import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BusyBeaverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem BusyBeaverHaltedBound_admissibility
    {stateCount machine emptyTape trace haltedOutput stepCount bound haltedLedger ledgerEndpoint
      package : BHist} :
    UnaryHistory stateCount -> UnaryHistory machine -> UnaryHistory emptyTape ->
      UnaryHistory haltedOutput -> UnaryHistory bound -> Cont machine emptyTape trace ->
        Cont trace haltedOutput stepCount -> Cont stepCount bound haltedLedger ->
          Cont stateCount haltedLedger ledgerEndpoint -> Cont ledgerEndpoint bound package ->
            UnaryHistory trace ∧ UnaryHistory stepCount ∧ UnaryHistory haltedLedger ∧
              UnaryHistory ledgerEndpoint ∧ UnaryHistory package ∧
                hsame trace (append machine emptyTape) ∧
                  hsame stepCount (append trace haltedOutput) ∧
                    hsame haltedLedger (append stepCount bound) ∧
                      hsame ledgerEndpoint (append stateCount haltedLedger) ∧
                        hsame package (append ledgerEndpoint bound) := by
  intro stateCountUnary machineUnary emptyTapeUnary haltedOutputUnary boundUnary
  intro traceRow stepCountRow haltedLedgerRow ledgerEndpointRow packageRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed machineUnary emptyTapeUnary traceRow
  have stepCountUnary : UnaryHistory stepCount :=
    unary_cont_closed traceUnary haltedOutputUnary stepCountRow
  have haltedLedgerUnary : UnaryHistory haltedLedger :=
    unary_cont_closed stepCountUnary boundUnary haltedLedgerRow
  have ledgerEndpointUnary : UnaryHistory ledgerEndpoint :=
    unary_cont_closed stateCountUnary haltedLedgerUnary ledgerEndpointRow
  have packageUnary : UnaryHistory package :=
    unary_cont_closed ledgerEndpointUnary boundUnary packageRow
  exact
    ⟨traceUnary, stepCountUnary, haltedLedgerUnary, ledgerEndpointUnary, packageUnary, traceRow,
      stepCountRow, haltedLedgerRow, ledgerEndpointRow, packageRow⟩

end BEDC.Derived.BusyBeaverUp
