import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BusyBeaverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem BusyBeaverHaltedBoundAdmissibility_halted_trace_surface
    {machine input trace output steps bound haltedLedger outputComparison stepComparison boundLedger
      fullLedger : BHist} :
    UnaryHistory machine -> UnaryHistory input -> UnaryHistory output -> UnaryHistory steps ->
      UnaryHistory bound -> Cont machine input trace -> Cont trace output haltedLedger ->
        Cont output bound outputComparison -> Cont steps bound stepComparison ->
          Cont haltedLedger outputComparison boundLedger ->
            Cont boundLedger stepComparison fullLedger ->
              UnaryHistory trace ∧ UnaryHistory haltedLedger ∧ UnaryHistory outputComparison ∧
                UnaryHistory stepComparison ∧ UnaryHistory boundLedger ∧ UnaryHistory fullLedger ∧
                  hsame haltedLedger (append trace output) ∧
                    hsame outputComparison (append output bound) ∧
                      hsame stepComparison (append steps bound) ∧
                        hsame boundLedger (append haltedLedger outputComparison) ∧
                          hsame fullLedger (append boundLedger stepComparison) := by
  intro machineUnary inputUnary outputUnary stepsUnary boundUnary traceRow haltedLedgerRow
  intro outputComparisonRow stepComparisonRow boundLedgerRow fullLedgerRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed machineUnary inputUnary traceRow
  have haltedLedgerUnary : UnaryHistory haltedLedger :=
    unary_cont_closed traceUnary outputUnary haltedLedgerRow
  have outputComparisonUnary : UnaryHistory outputComparison :=
    unary_cont_closed outputUnary boundUnary outputComparisonRow
  have stepComparisonUnary : UnaryHistory stepComparison :=
    unary_cont_closed stepsUnary boundUnary stepComparisonRow
  have boundLedgerUnary : UnaryHistory boundLedger :=
    unary_cont_closed haltedLedgerUnary outputComparisonUnary boundLedgerRow
  have fullLedgerUnary : UnaryHistory fullLedger :=
    unary_cont_closed boundLedgerUnary stepComparisonUnary fullLedgerRow
  exact
    ⟨traceUnary, haltedLedgerUnary, outputComparisonUnary, stepComparisonUnary,
      boundLedgerUnary, fullLedgerUnary, haltedLedgerRow, outputComparisonRow, stepComparisonRow,
      boundLedgerRow, fullLedgerRow⟩

end BEDC.Derived.BusyBeaverUp
