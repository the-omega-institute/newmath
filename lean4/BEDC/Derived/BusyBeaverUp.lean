import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.BusyBeaverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
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

theorem BusyBeaverPerMachineReadback_halted_readback_determinacy
    {machine input trace trace' output haltedLedger haltedLedger' steps fullLedger
      fullLedger' : BHist} :
    UnaryHistory machine -> UnaryHistory input -> UnaryHistory output -> UnaryHistory steps ->
      Cont machine input trace -> Cont machine input trace' ->
        Cont trace output haltedLedger -> Cont trace' output haltedLedger' ->
          Cont haltedLedger steps fullLedger -> Cont haltedLedger' steps fullLedger' ->
            UnaryHistory trace ∧ UnaryHistory trace' ∧ UnaryHistory haltedLedger ∧
              UnaryHistory haltedLedger' ∧ UnaryHistory fullLedger ∧ UnaryHistory fullLedger' ∧
                hsame trace trace' ∧ hsame haltedLedger haltedLedger' ∧
                  hsame fullLedger fullLedger' := by
  intro machineUnary inputUnary outputUnary stepsUnary traceRow traceRow'
  intro haltedLedgerRow haltedLedgerRow' fullLedgerRow fullLedgerRow'
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed machineUnary inputUnary traceRow
  have traceUnary' : UnaryHistory trace' :=
    unary_cont_closed machineUnary inputUnary traceRow'
  have traceSame : hsame trace trace' :=
    cont_deterministic traceRow traceRow'
  have haltedLedgerUnary : UnaryHistory haltedLedger :=
    unary_cont_closed traceUnary outputUnary haltedLedgerRow
  have haltedLedgerUnary' : UnaryHistory haltedLedger' :=
    unary_cont_closed traceUnary' outputUnary haltedLedgerRow'
  have haltedLedgerSame : hsame haltedLedger haltedLedger' :=
    cont_respects_hsame traceSame (hsame_refl output) haltedLedgerRow haltedLedgerRow'
  have fullLedgerUnary : UnaryHistory fullLedger :=
    unary_cont_closed haltedLedgerUnary stepsUnary fullLedgerRow
  have fullLedgerUnary' : UnaryHistory fullLedger' :=
    unary_cont_closed haltedLedgerUnary' stepsUnary fullLedgerRow'
  have fullLedgerSame : hsame fullLedger fullLedger' :=
    cont_respects_hsame haltedLedgerSame (hsame_refl steps) fullLedgerRow fullLedgerRow'
  exact
    ⟨traceUnary, traceUnary', haltedLedgerUnary, haltedLedgerUnary', fullLedgerUnary,
      fullLedgerUnary', traceSame, haltedLedgerSame, fullLedgerSame⟩

theorem BusyBeaverPerMachineReadback_halted_determinacy
    {machine input trace trace' output steps bound haltedLedger haltedLedger' outputComparison
      outputComparison' stepComparison stepComparison' boundLedger boundLedger' fullLedger
      fullLedger' : BHist} :
    UnaryHistory machine -> UnaryHistory input -> UnaryHistory output -> UnaryHistory steps ->
      UnaryHistory bound -> Cont machine input trace -> Cont machine input trace' ->
        Cont trace output haltedLedger -> Cont trace' output haltedLedger' ->
          Cont output bound outputComparison -> Cont output bound outputComparison' ->
            Cont steps bound stepComparison -> Cont steps bound stepComparison' ->
              Cont haltedLedger outputComparison boundLedger ->
                Cont haltedLedger' outputComparison' boundLedger' ->
                  Cont boundLedger stepComparison fullLedger ->
                    Cont boundLedger' stepComparison' fullLedger' ->
                      hsame trace trace' ∧ hsame haltedLedger haltedLedger' ∧
                        hsame outputComparison outputComparison' ∧
                          hsame stepComparison stepComparison' ∧
                            hsame boundLedger boundLedger' ∧ hsame fullLedger fullLedger' := by
  intro _machineUnary _inputUnary _outputUnary _stepsUnary _boundUnary traceRow traceRow'
  intro haltedLedgerRow haltedLedgerRow' outputComparisonRow outputComparisonRow'
  intro stepComparisonRow stepComparisonRow' boundLedgerRow boundLedgerRow'
  intro fullLedgerRow fullLedgerRow'
  have traceSame : hsame trace trace' :=
    cont_respects_hsame (hsame_refl machine) (hsame_refl input) traceRow traceRow'
  have haltedLedgerSame : hsame haltedLedger haltedLedger' :=
    cont_respects_hsame traceSame (hsame_refl output) haltedLedgerRow haltedLedgerRow'
  have outputComparisonSame : hsame outputComparison outputComparison' :=
    cont_respects_hsame (hsame_refl output) (hsame_refl bound) outputComparisonRow
      outputComparisonRow'
  have stepComparisonSame : hsame stepComparison stepComparison' :=
    cont_respects_hsame (hsame_refl steps) (hsame_refl bound) stepComparisonRow
      stepComparisonRow'
  have boundLedgerSame : hsame boundLedger boundLedger' :=
    cont_respects_hsame haltedLedgerSame outputComparisonSame boundLedgerRow boundLedgerRow'
  have fullLedgerSame : hsame fullLedger fullLedger' :=
    cont_respects_hsame boundLedgerSame stepComparisonSame fullLedgerRow fullLedgerRow'
  exact
    ⟨traceSame, haltedLedgerSame, outputComparisonSame, stepComparisonSame, boundLedgerSame,
      fullLedgerSame⟩

theorem BusyBeaverNonhaltingExclusion_obligation_surface
    {machine enumeration nonhaltBranch haltedTrace haltedOutput haltedLedger branchLedger
      publicLedger haltedPublicLedger : BHist} :
    UnaryHistory machine -> UnaryHistory enumeration -> UnaryHistory nonhaltBranch ->
      Cont enumeration machine branchLedger -> Cont branchLedger nonhaltBranch publicLedger ->
        hsame nonhaltBranch BHist.Empty -> Cont machine haltedOutput haltedTrace ->
          Cont haltedTrace haltedOutput haltedLedger ->
            Cont branchLedger (BHist.e1 haltedLedger) haltedPublicLedger ->
              hsame publicLedger haltedPublicLedger -> False := by
  intro _machineUnary _enumerationUnary _nonhaltUnary branchRow publicRow nonhaltEmpty
  intro _haltedTraceRow _haltedLedgerRow haltedPublicRow samePublic
  have publicToBranch : hsame publicLedger branchLedger :=
    cont_respects_hsame (hsame_refl branchLedger) nonhaltEmpty publicRow
      (cont_right_unit branchLedger)
  have haltedPublicToBranch : hsame haltedPublicLedger branchLedger :=
    hsame_trans (hsame_symm samePublic) publicToBranch
  have sameE1Empty : hsame (BHist.e1 haltedLedger) BHist.Empty :=
    cont_right_unit_unique
      (cont_result_hsame_transport haltedPublicRow haltedPublicToBranch)
  exact not_hsame_e1_empty sameE1Empty

theorem BusyBeaverHaltingLedger_scoped_namecert_surface
    {machine input trace output steps bound bound' haltedLedger outputBound outputBound'
      stepBound stepBound' ledger ledger' : BHist} :
    UnaryHistory machine -> UnaryHistory input -> UnaryHistory output -> UnaryHistory steps ->
      UnaryHistory bound -> hsame bound bound' -> Cont machine input trace ->
        Cont trace output haltedLedger -> Cont output bound outputBound ->
          Cont output bound' outputBound' -> Cont steps bound stepBound ->
            Cont steps bound' stepBound' -> Cont outputBound stepBound ledger ->
              Cont outputBound' stepBound' ledger' ->
                SemanticNameCert (fun row : BHist => UnaryHistory row ∧ hsame row ledger')
                  (fun row : BHist => UnaryHistory row ∧ hsame row ledger')
                  (fun row : BHist => UnaryHistory row ∧ hsame row ledger')
                  (fun row other : BHist => hsame row other ∧ UnaryHistory row ∧
                    UnaryHistory other) ∧
                    hsame ledger ledger' ∧ hsame haltedLedger (append trace output) := by
  intro machineUnary inputUnary outputUnary stepsUnary boundUnary sameBound traceRow
  intro haltedLedgerRow outputBoundRow outputBoundRow' stepBoundRow stepBoundRow'
  intro ledgerRow ledgerRow'
  have endpointData :=
    BusyBeaverPerMachineReadback_endpoint_exactness machineUnary inputUnary outputUnary
      stepsUnary boundUnary sameBound traceRow haltedLedgerRow outputBoundRow outputBoundRow'
      stepBoundRow stepBoundRow' ledgerRow ledgerRow'
  have ledgerUnary' : UnaryHistory ledger' :=
    endpointData.right.right.right.right.right.right.right.right.left
  have ledgerSame : hsame ledger ledger' :=
    endpointData.right.right.right.right.right.right.right.right.right.right.right.right
  have haltedExact : hsame haltedLedger (append trace output) :=
    endpointData.right.right.right.right.right.right.right.right.right.left
  have cert :
      SemanticNameCert (fun row : BHist => UnaryHistory row ∧ hsame row ledger')
        (fun row : BHist => UnaryHistory row ∧ hsame row ledger')
        (fun row : BHist => UnaryHistory row ∧ hsame row ledger')
        (fun row other : BHist => hsame row other ∧ UnaryHistory row ∧ UnaryHistory other) := {
    core := {
      carrier_inhabited := Exists.intro ledger' (And.intro ledgerUnary' (hsame_refl ledger'))
      equiv_refl := by
        intro h source
        exact And.intro (hsame_refl h) (And.intro source.left source.left)
      equiv_symm := by
        intro h k classified
        exact And.intro (hsame_symm classified.left)
          (And.intro classified.right.right classified.right.left)
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro (hsame_trans classifiedHK.left classifiedKR.left)
          (And.intro classifiedHK.right.left classifiedKR.right.right)
      carrier_respects_equiv := by
        intro h k classified source
        exact And.intro classified.right.right
          (hsame_trans (hsame_symm classified.left) source.right)
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }
  exact And.intro cert (And.intro ledgerSame haltedExact)

theorem BusyBeaverPerMachineHaltedReadback_determinacy
    {machine input trace trace' output output' steps steps' bound haltedLedger haltedLedger'
      outputComparison outputComparison' stepComparison stepComparison' boundLedger boundLedger'
      fullLedger fullLedger' : BHist} :
    UnaryHistory machine -> UnaryHistory input -> UnaryHistory output -> UnaryHistory output' ->
      UnaryHistory steps -> UnaryHistory steps' -> UnaryHistory bound ->
        Cont machine input trace -> Cont machine input trace' ->
          Cont trace output haltedLedger -> Cont trace' output' haltedLedger' ->
            hsame output output' -> hsame steps steps' ->
              Cont output bound outputComparison -> Cont output' bound outputComparison' ->
                Cont steps bound stepComparison -> Cont steps' bound stepComparison' ->
                  Cont haltedLedger outputComparison boundLedger ->
                    Cont haltedLedger' outputComparison' boundLedger' ->
                      Cont boundLedger stepComparison fullLedger ->
                        Cont boundLedger' stepComparison' fullLedger' ->
                          hsame trace trace' ∧ hsame haltedLedger haltedLedger' ∧
                            hsame outputComparison outputComparison' ∧
                              hsame stepComparison stepComparison' ∧
                                hsame boundLedger boundLedger' ∧ hsame fullLedger fullLedger' := by
  intro _machineUnary _inputUnary _outputUnary _outputUnary' _stepsUnary _stepsUnary'
  intro _boundUnary traceRow traceRow' haltedLedgerRow haltedLedgerRow'
  intro sameOutput sameSteps outputComparisonRow outputComparisonRow'
  intro stepComparisonRow stepComparisonRow' boundLedgerRow boundLedgerRow'
  intro fullLedgerRow fullLedgerRow'
  have sameTrace : hsame trace trace' :=
    cont_respects_hsame (hsame_refl machine) (hsame_refl input) traceRow traceRow'
  have sameHaltedLedger : hsame haltedLedger haltedLedger' :=
    cont_respects_hsame sameTrace sameOutput haltedLedgerRow haltedLedgerRow'
  have sameOutputComparison : hsame outputComparison outputComparison' :=
    cont_respects_hsame sameOutput (hsame_refl bound) outputComparisonRow outputComparisonRow'
  have sameStepComparison : hsame stepComparison stepComparison' :=
    cont_respects_hsame sameSteps (hsame_refl bound) stepComparisonRow stepComparisonRow'
  have sameBoundLedger : hsame boundLedger boundLedger' :=
    cont_respects_hsame sameHaltedLedger sameOutputComparison boundLedgerRow boundLedgerRow'
  have sameFullLedger : hsame fullLedger fullLedger' :=
    cont_respects_hsame sameBoundLedger sameStepComparison fullLedgerRow fullLedgerRow'
  exact
    ⟨sameTrace, sameHaltedLedger, sameOutputComparison, sameStepComparison,
      sameBoundLedger, sameFullLedger⟩

end BEDC.Derived.BusyBeaverUp
