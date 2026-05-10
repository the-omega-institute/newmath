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

inductive TuringMachineHaltedTrace (halted : BHist) : List BHist → BHist → Prop where
  | endpoint : TuringMachineHaltedTrace halted [] halted
  | repeatRow {row : BHist} {rows : List BHist} {endpoint : BHist} :
      hsame row halted →
        TuringMachineHaltedTrace halted rows endpoint →
          TuringMachineHaltedTrace halted (row :: rows) endpoint

theorem TuringMachineHaltedTrace_repeat_obligation {halted : BHist} {rows : List BHist}
    {endpoint : BHist} :
    TuringMachineHaltedTrace halted rows endpoint →
      UnaryHistory halted →
        (∀ row : BHist, List.Mem row rows → hsame row halted) ∧ UnaryHistory endpoint := by
  intro trace haltedUnary
  induction trace with
  | endpoint =>
      constructor
      · intro row rowMem
        cases rowMem
      · exact haltedUnary
  | repeatRow rowSame _ ih =>
      have tailRows := ih
      constructor
      · intro row rowMem
        cases rowMem with
        | head =>
            exact rowSame
        | tail _ tailMem =>
            exact tailRows.left row tailMem
      · exact tailRows.right

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

theorem TuringMachineObligationSurface_bounded_trace_ledger
    {state tape head bound configuration trace readback bounded endpoint : BHist} :
    UnaryHistory state -> UnaryHistory tape -> UnaryHistory head -> UnaryHistory bound ->
      Cont state tape configuration -> Cont configuration head trace -> Cont tape head readback ->
        Cont trace readback bounded -> Cont bounded bound endpoint ->
          UnaryHistory configuration ∧ UnaryHistory trace ∧ UnaryHistory readback ∧
            UnaryHistory bounded ∧ UnaryHistory endpoint ∧ hsame configuration (append state tape) ∧
              hsame trace (append configuration head) ∧ hsame readback (append tape head) ∧
                hsame bounded (append trace readback) ∧ hsame endpoint (append bounded bound) := by
  intro stateUnary tapeUnary headUnary boundUnary configurationRow traceRow readbackRow boundedRow
    endpointRow
  have configurationUnary : UnaryHistory configuration :=
    unary_cont_closed stateUnary tapeUnary configurationRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed configurationUnary headUnary traceRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed tapeUnary headUnary readbackRow
  have boundedUnary : UnaryHistory bounded :=
    unary_cont_closed traceUnary readbackUnary boundedRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed boundedUnary boundUnary endpointRow
  exact
    ⟨configurationUnary, traceUnary, readbackUnary, boundedUnary, endpointUnary, configurationRow,
      traceRow, readbackRow, boundedRow, endpointRow⟩

theorem TuringMachineBoundedReadback_soundness
    {trace tape head readback bound bounded output : BHist} :
    UnaryHistory trace ->
      UnaryHistory tape ->
        UnaryHistory head ->
          UnaryHistory bound ->
            Cont tape head readback ->
              Cont trace readback bounded ->
                Cont bounded bound output ->
                  UnaryHistory readback ∧ UnaryHistory bounded ∧ UnaryHistory output ∧
                    hsame readback (append tape head) ∧
                      hsame bounded (append trace readback) ∧
                        hsame output (append bounded bound) := by
  intro traceUnary tapeUnary headUnary boundUnary readbackRow boundedRow outputRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed tapeUnary headUnary readbackRow
  have boundedUnary : UnaryHistory bounded :=
    unary_cont_closed traceUnary readbackUnary boundedRow
  have outputUnary : UnaryHistory output :=
    unary_cont_closed boundedUnary boundUnary outputRow
  exact
    ⟨readbackUnary, boundedUnary, outputUnary, readbackRow, boundedRow, outputRow⟩

theorem TuringMachineHaltedTrace_ledger_exactness {halted : BHist} {rows : List BHist}
    {endpoint ledger : BHist} :
    TuringMachineHaltedTrace halted rows endpoint -> UnaryHistory halted ->
      Cont endpoint halted ledger ->
        (forall row : BHist, List.Mem row rows -> hsame row halted) ∧
          UnaryHistory endpoint ∧ UnaryHistory ledger ∧
            hsame ledger (append endpoint halted) := by
  intro haltedTrace haltedUnary ledgerRow
  have repeatedRows :=
    TuringMachineHaltedTrace_repeat_obligation haltedTrace haltedUnary
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed repeatedRows.right haltedUnary ledgerRow
  exact ⟨repeatedRows.left, repeatedRows.right, ledgerUnary, ledgerRow⟩

theorem TuringMachineObligationSurface_rows
    {state tape head bound configuration trace endpoint halted readback finalLedger : BHist}
    {haltRows : List BHist} :
    UnaryHistory state -> UnaryHistory tape -> UnaryHistory head -> UnaryHistory bound ->
      Cont state tape configuration -> Cont configuration head trace -> Cont trace bound endpoint ->
        TuringMachineHaltedTrace halted haltRows endpoint -> Cont endpoint readback finalLedger ->
          UnaryHistory readback -> UnaryHistory halted ->
            UnaryHistory configuration ∧ UnaryHistory trace ∧ UnaryHistory endpoint ∧
              UnaryHistory finalLedger ∧
                (forall row : BHist, List.Mem row haltRows -> hsame row halted) ∧
                  hsame finalLedger (append endpoint readback) := by
  intro stateUnary tapeUnary headUnary boundUnary configurationRow traceRow endpointRow
  intro haltedTrace finalLedgerRow readbackUnary haltedUnary
  have configurationSurface :=
    TuringMachineConfigurationTraceCarrier_configuration_trace_surface stateUnary tapeUnary
      headUnary boundUnary configurationRow traceRow endpointRow
  have repeatedRows :=
    TuringMachineHaltedTrace_repeat_obligation haltedTrace haltedUnary
  have finalLedgerUnary : UnaryHistory finalLedger :=
    unary_cont_closed configurationSurface.right.right.left readbackUnary finalLedgerRow
  exact
    ⟨configurationSurface.left, configurationSurface.right.left,
      configurationSurface.right.right.left, finalLedgerUnary, repeatedRows.left, finalLedgerRow⟩

theorem TuringMachineTraceSourceObligation_source_rows
    {state tape head bound alphabet configuration trace endpoint source : BHist} :
    UnaryHistory state -> UnaryHistory tape -> UnaryHistory head -> UnaryHistory bound ->
      UnaryHistory alphabet -> Cont state tape configuration -> Cont configuration head trace ->
        Cont trace bound endpoint -> Cont alphabet endpoint source ->
          UnaryHistory configuration ∧ UnaryHistory trace ∧ UnaryHistory endpoint ∧
            UnaryHistory source ∧ hsame configuration (append state tape) ∧
              hsame trace (append configuration head) ∧ hsame endpoint (append trace bound) ∧
                hsame source (append alphabet endpoint) := by
  intro stateUnary tapeUnary headUnary boundUnary alphabetUnary configurationRow traceRow endpointRow
    sourceRow
  have configurationSurface :=
    TuringMachineConfigurationTraceCarrier_configuration_trace_surface stateUnary tapeUnary
      headUnary boundUnary configurationRow traceRow endpointRow
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed alphabetUnary configurationSurface.right.right.left sourceRow
  exact
    ⟨configurationSurface.left, configurationSurface.right.left,
      configurationSurface.right.right.left, sourceUnary, configurationSurface.right.right.right.left,
      configurationSurface.right.right.right.right.left,
      configurationSurface.right.right.right.right.right, sourceRow⟩

theorem TuringMachineLedgerExactnessObligation_rows_and_boundary
    {halted endpoint readback ledger boundary : BHist} {haltRows : List BHist} :
    TuringMachineHaltedTrace halted haltRows endpoint -> UnaryHistory halted ->
      UnaryHistory readback -> Cont endpoint readback ledger -> Cont ledger halted boundary ->
        (forall row : BHist, List.Mem row haltRows -> hsame row halted) ∧
          UnaryHistory endpoint ∧ UnaryHistory ledger ∧ UnaryHistory boundary ∧
            hsame ledger (append endpoint readback) ∧ hsame boundary (append ledger halted) := by
  intro haltedTrace haltedUnary readbackUnary ledgerRow boundaryRow
  have repeatedRows :=
    TuringMachineHaltedTrace_repeat_obligation haltedTrace haltedUnary
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed repeatedRows.right readbackUnary ledgerRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed ledgerUnary haltedUnary boundaryRow
  exact ⟨repeatedRows.left, repeatedRows.right, ledgerUnary, boundaryUnary, ledgerRow, boundaryRow⟩

end BEDC.Derived.TuringMachineUp
