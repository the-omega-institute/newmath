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

theorem BusyBeaverBoundMonotonicity_bound_transport
    {output steps bound bound' outputBound outputBound' stepBound stepBound' ledger
      ledger' : BHist} :
    UnaryHistory output -> UnaryHistory steps -> UnaryHistory bound -> hsame bound bound' ->
      Cont output bound outputBound -> Cont output bound' outputBound' ->
        Cont steps bound stepBound -> Cont steps bound' stepBound' ->
          Cont outputBound stepBound ledger -> Cont outputBound' stepBound' ledger' ->
            UnaryHistory bound' ∧ UnaryHistory outputBound ∧ UnaryHistory outputBound' ∧
              UnaryHistory stepBound ∧ UnaryHistory stepBound' ∧ UnaryHistory ledger ∧
                UnaryHistory ledger' ∧ hsame outputBound outputBound' ∧
                  hsame stepBound stepBound' ∧ hsame ledger ledger' := by
  intro outputUnary stepsUnary boundUnary sameBound outputBoundRow outputBoundRow'
  intro stepBoundRow stepBoundRow' ledgerRow ledgerRow'
  have boundUnary' : UnaryHistory bound' :=
    unary_transport boundUnary sameBound
  have outputBoundUnary : UnaryHistory outputBound :=
    unary_cont_closed outputUnary boundUnary outputBoundRow
  have outputBoundUnary' : UnaryHistory outputBound' :=
    unary_cont_closed outputUnary boundUnary' outputBoundRow'
  have stepBoundUnary : UnaryHistory stepBound :=
    unary_cont_closed stepsUnary boundUnary stepBoundRow
  have stepBoundUnary' : UnaryHistory stepBound' :=
    unary_cont_closed stepsUnary boundUnary' stepBoundRow'
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed outputBoundUnary stepBoundUnary ledgerRow
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed outputBoundUnary' stepBoundUnary' ledgerRow'
  have outputBoundSame : hsame outputBound outputBound' :=
    cont_respects_hsame (hsame_refl output) sameBound outputBoundRow outputBoundRow'
  have stepBoundSame : hsame stepBound stepBound' :=
    cont_respects_hsame (hsame_refl steps) sameBound stepBoundRow stepBoundRow'
  have ledgerSame : hsame ledger ledger' :=
    cont_respects_hsame outputBoundSame stepBoundSame ledgerRow ledgerRow'
  exact
    ⟨boundUnary', outputBoundUnary, outputBoundUnary', stepBoundUnary, stepBoundUnary',
      ledgerUnary, ledgerUnary', outputBoundSame, stepBoundSame, ledgerSame⟩

end BEDC.Derived.BusyBeaverUp
