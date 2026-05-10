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

theorem BusyBeaverEnumerationCompleteness_finite_ledger_surface
    {stateCount machine enumeration branch haltedLedger outsideLedger coverageLedger
      package : BHist} :
    UnaryHistory stateCount -> UnaryHistory machine -> UnaryHistory branch ->
      Cont stateCount machine enumeration -> Cont enumeration branch haltedLedger ->
        Cont machine branch outsideLedger -> Cont haltedLedger outsideLedger coverageLedger ->
          Cont coverageLedger stateCount package ->
            UnaryHistory enumeration ∧ UnaryHistory haltedLedger ∧ UnaryHistory outsideLedger ∧
              UnaryHistory coverageLedger ∧ UnaryHistory package ∧
                hsame enumeration (append stateCount machine) ∧
                  hsame haltedLedger (append enumeration branch) ∧
                    hsame outsideLedger (append machine branch) ∧
                      hsame coverageLedger (append haltedLedger outsideLedger) ∧
                        hsame package (append coverageLedger stateCount) := by
  intro stateCountUnary machineUnary branchUnary enumerationRow haltedLedgerRow outsideLedgerRow
  intro coverageLedgerRow packageRow
  have enumerationUnary : UnaryHistory enumeration :=
    unary_cont_closed stateCountUnary machineUnary enumerationRow
  have haltedLedgerUnary : UnaryHistory haltedLedger :=
    unary_cont_closed enumerationUnary branchUnary haltedLedgerRow
  have outsideLedgerUnary : UnaryHistory outsideLedger :=
    unary_cont_closed machineUnary branchUnary outsideLedgerRow
  have coverageLedgerUnary : UnaryHistory coverageLedger :=
    unary_cont_closed haltedLedgerUnary outsideLedgerUnary coverageLedgerRow
  have packageUnary : UnaryHistory package :=
    unary_cont_closed coverageLedgerUnary stateCountUnary packageRow
  exact
    ⟨enumerationUnary, haltedLedgerUnary, outsideLedgerUnary, coverageLedgerUnary, packageUnary,
      enumerationRow, haltedLedgerRow, outsideLedgerRow, coverageLedgerRow, packageRow⟩

theorem BusyBeaverEnumerationCompleteness_finite_coverage
    {stateCount machine enumeration listed branch coverage publicLedger : BHist} :
    UnaryHistory stateCount -> UnaryHistory machine -> UnaryHistory enumeration ->
      Cont stateCount machine listed -> Cont enumeration listed branch ->
        Cont machine branch coverage -> Cont coverage enumeration publicLedger ->
          UnaryHistory listed ∧ UnaryHistory branch ∧ UnaryHistory coverage ∧
            UnaryHistory publicLedger ∧ hsame listed (append stateCount machine) ∧
              hsame branch (append enumeration listed) ∧ hsame coverage (append machine branch) ∧
                hsame publicLedger (append coverage enumeration) := by
  intro stateCountUnary machineUnary enumerationUnary listedRow branchRow coverageRow
  intro publicLedgerRow
  have listedUnary : UnaryHistory listed :=
    unary_cont_closed stateCountUnary machineUnary listedRow
  have branchUnary : UnaryHistory branch :=
    unary_cont_closed enumerationUnary listedUnary branchRow
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed machineUnary branchUnary coverageRow
  have publicLedgerUnary : UnaryHistory publicLedger :=
    unary_cont_closed coverageUnary enumerationUnary publicLedgerRow
  exact
    ⟨listedUnary, branchUnary, coverageUnary, publicLedgerUnary, listedRow, branchRow,
      coverageRow, publicLedgerRow⟩

theorem BusyBeaverEnumerationCompleteness_append_coverage
    {left right : List BHist} {machine bound ledger : BHist} :
    List.Mem machine (left ++ right) ->
      (forall m : BHist, List.Mem m left -> UnaryHistory m) ->
        (forall m : BHist, List.Mem m right -> UnaryHistory m) ->
          UnaryHistory bound -> Cont machine bound ledger ->
            UnaryHistory machine ∧ UnaryHistory ledger ∧ hsame ledger (append machine bound) := by
  intro machineMem leftCoverage rightCoverage boundUnary ledgerRow
  induction left with
  | nil =>
      have machineUnary : UnaryHistory machine :=
        rightCoverage machine machineMem
      have ledgerUnary : UnaryHistory ledger :=
        unary_cont_closed machineUnary boundUnary ledgerRow
      exact ⟨machineUnary, ledgerUnary, ledgerRow⟩
  | cons head tail ih =>
      cases machineMem with
      | head =>
          have machineUnary : UnaryHistory machine :=
            leftCoverage machine (List.Mem.head tail)
          have ledgerUnary : UnaryHistory ledger :=
            unary_cont_closed machineUnary boundUnary ledgerRow
          exact ⟨machineUnary, ledgerUnary, ledgerRow⟩
      | tail _ tailMem =>
          have tailCoverage : forall m : BHist, List.Mem m tail -> UnaryHistory m := by
            intro m memTail
            exact leftCoverage m (List.Mem.tail head memTail)
          exact ih tailMem tailCoverage

theorem BusyBeaverPerMachineReadback_membership_exactness
    {left right : List BHist}
    {machine input trace output steps bound haltedLedger outputComparison stepComparison
      boundLedger fullLedger : BHist} :
    List.Mem machine (left ++ right) ->
      (forall m : BHist, List.Mem m left -> UnaryHistory m) ->
        (forall m : BHist, List.Mem m right -> UnaryHistory m) ->
          UnaryHistory input ->
            UnaryHistory output ->
              UnaryHistory steps ->
                UnaryHistory bound ->
                  Cont machine input trace ->
                    Cont trace output haltedLedger ->
                      Cont output bound outputComparison ->
                        Cont steps bound stepComparison ->
                          Cont haltedLedger outputComparison boundLedger ->
                            Cont boundLedger stepComparison fullLedger ->
                              UnaryHistory machine ∧ UnaryHistory trace ∧
                                UnaryHistory haltedLedger ∧ UnaryHistory outputComparison ∧
                                  UnaryHistory stepComparison ∧ UnaryHistory boundLedger ∧
                                    UnaryHistory fullLedger ∧
                                      hsame fullLedger (append boundLedger stepComparison) := by
  intro machineMem leftCoverage rightCoverage inputUnary outputUnary stepsUnary boundUnary
  intro traceRow haltedLedgerRow outputComparisonRow stepComparisonRow boundLedgerRow
  intro fullLedgerRow
  have machineUnary : UnaryHistory machine := by
    induction left with
    | nil =>
        exact rightCoverage machine machineMem
    | cons head tail ih =>
        cases machineMem with
        | head =>
            exact leftCoverage machine (List.Mem.head tail)
        | tail _ tailMem =>
            have tailCoverage : forall m : BHist, List.Mem m tail -> UnaryHistory m := by
              intro m memTail
              exact leftCoverage m (List.Mem.tail head memTail)
            exact ih tailMem tailCoverage
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
    ⟨machineUnary, traceUnary, haltedLedgerUnary, outputComparisonUnary, stepComparisonUnary,
      boundLedgerUnary, fullLedgerUnary, fullLedgerRow⟩

theorem BusyBeaverPerMachineReadback_endpoint_exactness
    {machine input trace output steps bound bound' haltedLedger outputBound outputBound'
      stepBound stepBound' ledger ledger' : BHist} :
    UnaryHistory machine -> UnaryHistory input -> UnaryHistory output -> UnaryHistory steps ->
      UnaryHistory bound -> hsame bound bound' -> Cont machine input trace ->
        Cont trace output haltedLedger -> Cont output bound outputBound ->
          Cont output bound' outputBound' -> Cont steps bound stepBound ->
            Cont steps bound' stepBound' -> Cont outputBound stepBound ledger ->
              Cont outputBound' stepBound' ledger' ->
                UnaryHistory trace ∧ UnaryHistory haltedLedger ∧ UnaryHistory bound' ∧
                  UnaryHistory outputBound ∧ UnaryHistory outputBound' ∧ UnaryHistory stepBound ∧
                    UnaryHistory stepBound' ∧ UnaryHistory ledger ∧ UnaryHistory ledger' ∧
                      hsame haltedLedger (append trace output) ∧
                        hsame outputBound outputBound' ∧ hsame stepBound stepBound' ∧
                          hsame ledger ledger' := by
  intro machineUnary inputUnary outputUnary stepsUnary boundUnary sameBound traceRow
  intro haltedLedgerRow outputBoundRow outputBoundRow' stepBoundRow stepBoundRow'
  intro ledgerRow ledgerRow'
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed machineUnary inputUnary traceRow
  have haltedLedgerUnary : UnaryHistory haltedLedger :=
    unary_cont_closed traceUnary outputUnary haltedLedgerRow
  have boundData :=
    BusyBeaverBoundMonotonicity_bound_transport outputUnary stepsUnary boundUnary sameBound
      outputBoundRow outputBoundRow' stepBoundRow stepBoundRow' ledgerRow ledgerRow'
  exact
    ⟨traceUnary, haltedLedgerUnary, boundData.left, boundData.right.left,
      boundData.right.right.left, boundData.right.right.right.left,
      boundData.right.right.right.right.left, boundData.right.right.right.right.right.left,
      boundData.right.right.right.right.right.right.left, haltedLedgerRow,
      boundData.right.right.right.right.right.right.right.left,
      boundData.right.right.right.right.right.right.right.right.left,
      boundData.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.BusyBeaverUp
