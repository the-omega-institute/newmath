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

theorem TuringMachineSourceClassifierObligation_source_classifier_surface
    {state tape head table trace readback source transported : BHist} :
    UnaryHistory state -> UnaryHistory tape -> UnaryHistory head -> UnaryHistory table ->
      Cont state tape source -> Cont source head trace -> Cont tape head readback ->
        Cont trace table transported ->
          UnaryHistory source ∧ UnaryHistory trace ∧ UnaryHistory readback ∧
            UnaryHistory transported ∧ hsame source (append state tape) ∧
              hsame trace (append source head) ∧ hsame readback (append tape head) ∧
                hsame transported (append trace table) := by
  intro stateUnary tapeUnary headUnary tableUnary sourceRow traceRow readbackRow transportedRow
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed stateUnary tapeUnary sourceRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed sourceUnary headUnary traceRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed tapeUnary headUnary readbackRow
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed traceUnary tableUnary transportedRow
  exact
    ⟨sourceUnary, traceUnary, readbackUnary, transportedUnary, sourceRow, traceRow, readbackRow,
      transportedRow⟩

theorem TuringMachineSourceClassifierObligation_cont_transport
    {state state' tape tape' head head' bound bound' configuration configuration' trace trace'
      endpoint endpoint' : BHist} :
    UnaryHistory state -> UnaryHistory tape -> UnaryHistory head -> UnaryHistory bound ->
      Cont state tape configuration -> Cont configuration head trace ->
        Cont trace bound endpoint -> hsame state state' -> hsame tape tape' ->
          hsame head head' -> hsame bound bound' -> Cont state' tape' configuration' ->
            Cont configuration' head' trace' -> Cont trace' bound' endpoint' ->
              UnaryHistory configuration ∧ UnaryHistory trace ∧ UnaryHistory endpoint ∧
                UnaryHistory configuration' ∧ UnaryHistory trace' ∧ UnaryHistory endpoint' ∧
                  hsame configuration configuration' ∧ hsame trace trace' ∧
                    hsame endpoint endpoint' := by
  intro stateUnary tapeUnary headUnary boundUnary configurationRow traceRow endpointRow sameState
    sameTape sameHead sameBound configurationRow' traceRow' endpointRow'
  have configurationUnary : UnaryHistory configuration :=
    unary_cont_closed stateUnary tapeUnary configurationRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed configurationUnary headUnary traceRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed traceUnary boundUnary endpointRow
  have stateUnary' : UnaryHistory state' :=
    unary_transport stateUnary sameState
  have tapeUnary' : UnaryHistory tape' :=
    unary_transport tapeUnary sameTape
  have headUnary' : UnaryHistory head' :=
    unary_transport headUnary sameHead
  have boundUnary' : UnaryHistory bound' :=
    unary_transport boundUnary sameBound
  have configurationUnary' : UnaryHistory configuration' :=
    unary_cont_closed stateUnary' tapeUnary' configurationRow'
  have traceUnary' : UnaryHistory trace' :=
    unary_cont_closed configurationUnary' headUnary' traceRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed traceUnary' boundUnary' endpointRow'
  have sameConfiguration : hsame configuration configuration' :=
    cont_respects_hsame sameState sameTape configurationRow configurationRow'
  have sameTrace : hsame trace trace' :=
    cont_respects_hsame sameConfiguration sameHead traceRow traceRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameTrace sameBound endpointRow endpointRow'
  exact
    ⟨configurationUnary, traceUnary, endpointUnary, configurationUnary', traceUnary',
      endpointUnary', sameConfiguration, sameTrace, sameEndpoint⟩

theorem TuringMachineSourceClassifier_cont_transport
    {state tape head table configuration trace next nextPrime readback readbackPrime ledger
      ledgerPrime : BHist} :
    UnaryHistory state -> UnaryHistory tape -> UnaryHistory head -> UnaryHistory table ->
      Cont state tape configuration -> Cont configuration head trace ->
        Cont configuration table next -> hsame next nextPrime -> Cont tape head readback ->
          hsame readback readbackPrime -> Cont trace next ledger ->
            hsame ledger ledgerPrime ->
              UnaryHistory configuration ∧ UnaryHistory trace ∧ UnaryHistory nextPrime ∧
                UnaryHistory readbackPrime ∧ UnaryHistory ledgerPrime ∧
                  hsame configuration (append state tape) ∧
                    hsame trace (append configuration head) ∧
                      hsame readbackPrime readback ∧ hsame ledgerPrime ledger := by
  intro stateUnary tapeUnary headUnary tableUnary configurationRow traceRow nextRow sameNext
  intro readbackRow sameReadback ledgerRow sameLedger
  have configurationUnary : UnaryHistory configuration :=
    unary_cont_closed stateUnary tapeUnary configurationRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed configurationUnary headUnary traceRow
  have nextUnary : UnaryHistory next :=
    unary_cont_closed configurationUnary tableUnary nextRow
  have nextPrimeUnary : UnaryHistory nextPrime :=
    unary_transport nextUnary sameNext
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed tapeUnary headUnary readbackRow
  have readbackPrimeUnary : UnaryHistory readbackPrime :=
    unary_transport readbackUnary sameReadback
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed traceUnary nextUnary ledgerRow
  have ledgerPrimeUnary : UnaryHistory ledgerPrime :=
    unary_transport ledgerUnary sameLedger
  exact
    ⟨configurationUnary, traceUnary, nextPrimeUnary, readbackPrimeUnary, ledgerPrimeUnary,
      configurationRow, traceRow, hsame_symm sameReadback, hsame_symm sameLedger⟩

theorem TuringMachineBoundedReadbackSoundness_endpoint_transport
    {tape tape' head head' readback readback' trace trace' bounded bounded' : BHist} :
    UnaryHistory tape -> UnaryHistory head -> UnaryHistory trace -> Cont tape head readback ->
      Cont trace readback bounded -> hsame tape tape' -> hsame head head' ->
        hsame trace trace' -> Cont tape' head' readback' ->
          Cont trace' readback' bounded' ->
            UnaryHistory readback ∧ UnaryHistory bounded ∧ UnaryHistory readback' ∧
              UnaryHistory bounded' ∧ hsame readback readback' ∧ hsame bounded bounded' := by
  intro tapeUnary headUnary traceUnary readbackRow boundedRow sameTape sameHead sameTrace
    readbackRow' boundedRow'
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed tapeUnary headUnary readbackRow
  have boundedUnary : UnaryHistory bounded :=
    unary_cont_closed traceUnary readbackUnary boundedRow
  have tapeUnary' : UnaryHistory tape' :=
    unary_transport tapeUnary sameTape
  have headUnary' : UnaryHistory head' :=
    unary_transport headUnary sameHead
  have traceUnary' : UnaryHistory trace' :=
    unary_transport traceUnary sameTrace
  have readbackUnary' : UnaryHistory readback' :=
    unary_cont_closed tapeUnary' headUnary' readbackRow'
  have boundedUnary' : UnaryHistory bounded' :=
    unary_cont_closed traceUnary' readbackUnary' boundedRow'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameTape sameHead readbackRow readbackRow'
  have sameBounded : hsame bounded bounded' :=
    cont_respects_hsame sameTrace sameReadback boundedRow boundedRow'
  exact
    ⟨readbackUnary, boundedUnary, readbackUnary', boundedUnary', sameReadback, sameBounded⟩

theorem TuringMachineSourceClassifier_obligation
    {state tape head table configuration trace next readback bounded source : BHist} :
    UnaryHistory state -> UnaryHistory tape -> UnaryHistory head -> UnaryHistory table ->
      Cont state tape configuration -> Cont configuration head trace -> Cont trace table next ->
        Cont tape head readback -> Cont next readback bounded -> Cont trace bounded source ->
          UnaryHistory configuration ∧ UnaryHistory trace ∧ UnaryHistory next ∧
            UnaryHistory readback ∧ UnaryHistory bounded ∧ UnaryHistory source ∧
              hsame configuration (append state tape) ∧ hsame trace (append configuration head) ∧
                hsame next (append trace table) ∧ hsame readback (append tape head) ∧
                  hsame bounded (append next readback) ∧
                    hsame source (append trace bounded) := by
  intro stateUnary tapeUnary headUnary tableUnary
  intro configurationRow traceRow nextRow readbackRow boundedRow sourceRow
  have configurationUnary : UnaryHistory configuration :=
    unary_cont_closed stateUnary tapeUnary configurationRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed configurationUnary headUnary traceRow
  have nextUnary : UnaryHistory next :=
    unary_cont_closed traceUnary tableUnary nextRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed tapeUnary headUnary readbackRow
  have boundedUnary : UnaryHistory bounded :=
    unary_cont_closed nextUnary readbackUnary boundedRow
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed traceUnary boundedUnary sourceRow
  exact
    ⟨configurationUnary, traceUnary, nextUnary, readbackUnary, boundedUnary, sourceUnary,
      configurationRow, traceRow, nextRow, readbackRow, boundedRow, sourceRow⟩

theorem TuringMachineNameCertSurface_obligation
    {state tape head bound configuration trace endpoint halted readback finalLedger boundary
      source : BHist}
    {haltRows : List BHist} :
    UnaryHistory state -> UnaryHistory tape -> UnaryHistory head -> UnaryHistory bound ->
      Cont state tape configuration -> Cont configuration head trace -> Cont trace bound endpoint ->
        TuringMachineHaltedTrace halted haltRows endpoint -> Cont endpoint readback finalLedger ->
          Cont finalLedger halted boundary -> Cont configuration boundary source ->
            UnaryHistory readback -> UnaryHistory halted ->
              UnaryHistory configuration ∧ UnaryHistory trace ∧ UnaryHistory endpoint ∧
                UnaryHistory finalLedger ∧ UnaryHistory boundary ∧ UnaryHistory source ∧
                  (forall row : BHist, List.Mem row haltRows -> hsame row halted) ∧
                    hsame finalLedger (append endpoint readback) ∧
                      hsame boundary (append finalLedger halted) ∧
                        hsame source (append configuration boundary) := by
  intro stateUnary tapeUnary headUnary boundUnary configurationRow traceRow endpointRow
  intro haltedTrace finalLedgerRow boundaryRow sourceRow readbackUnary haltedUnary
  have configurationSurface :=
    TuringMachineConfigurationTraceCarrier_configuration_trace_surface stateUnary tapeUnary
      headUnary boundUnary configurationRow traceRow endpointRow
  have haltedRowsSurface :=
    TuringMachineHaltedTrace_repeat_obligation haltedTrace haltedUnary
  have finalLedgerUnary : UnaryHistory finalLedger :=
    unary_cont_closed configurationSurface.right.right.left readbackUnary finalLedgerRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed finalLedgerUnary haltedUnary boundaryRow
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed configurationSurface.left boundaryUnary sourceRow
  exact
    ⟨configurationSurface.left, configurationSurface.right.left,
      configurationSurface.right.right.left, finalLedgerUnary, boundaryUnary, sourceUnary,
      haltedRowsSurface.left, finalLedgerRow, boundaryRow, sourceRow⟩

theorem TuringMachineNameCertSurfaceObligation_public_surface
    {state tape head bound configuration trace readback bounded endpoint halted ledger publicSurface :
      BHist} {haltRows : List BHist} :
    UnaryHistory state -> UnaryHistory tape -> UnaryHistory head -> UnaryHistory bound ->
      UnaryHistory halted -> Cont state tape configuration -> Cont configuration head trace ->
        Cont tape head readback -> Cont trace readback bounded -> Cont bounded bound endpoint ->
          TuringMachineHaltedTrace halted haltRows endpoint -> Cont endpoint halted ledger ->
            Cont ledger bounded publicSurface ->
              UnaryHistory configuration ∧ UnaryHistory trace ∧ UnaryHistory readback ∧
                UnaryHistory bounded ∧ UnaryHistory endpoint ∧ UnaryHistory ledger ∧
                  UnaryHistory publicSurface ∧ hsame publicSurface (append ledger bounded) := by
  intro stateUnary tapeUnary headUnary boundUnary haltedUnary configurationRow traceRow readbackRow
  intro boundedRow endpointRow haltedTrace ledgerRow publicSurfaceRow
  have configurationUnary : UnaryHistory configuration :=
    unary_cont_closed stateUnary tapeUnary configurationRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed configurationUnary headUnary traceRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed tapeUnary headUnary readbackRow
  have boundedUnary : UnaryHistory bounded :=
    unary_cont_closed traceUnary readbackUnary boundedRow
  have endpointUnary : UnaryHistory endpoint :=
    (TuringMachineHaltedTrace_repeat_obligation haltedTrace haltedUnary).right
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed endpointUnary haltedUnary ledgerRow
  have publicSurfaceUnary : UnaryHistory publicSurface :=
    unary_cont_closed ledgerUnary boundedUnary publicSurfaceRow
  exact
    ⟨configurationUnary, traceUnary, readbackUnary, boundedUnary, endpointUnary, ledgerUnary,
      publicSurfaceUnary, publicSurfaceRow⟩

theorem TuringMachineLedgerExactnessObligation_no_external_rows
    {state tape head bound configuration trace endpoint halted readback finalLedger
      publicLedger : BHist}
    {haltRows : List BHist} :
    UnaryHistory state -> UnaryHistory tape -> UnaryHistory head -> UnaryHistory bound ->
      Cont state tape configuration -> Cont configuration head trace -> Cont trace bound endpoint ->
        TuringMachineHaltedTrace halted haltRows endpoint -> Cont endpoint readback finalLedger ->
          UnaryHistory readback -> UnaryHistory halted -> Cont finalLedger halted publicLedger ->
            UnaryHistory publicLedger ∧
              (forall row : BHist, List.Mem row haltRows -> hsame row halted) ∧
                hsame finalLedger (append endpoint readback) ∧
                  hsame publicLedger (append finalLedger halted) := by
  intro stateUnary tapeUnary headUnary boundUnary configurationRow traceRow endpointRow haltedTrace
  intro finalLedgerRow readbackUnary haltedUnary publicLedgerRow
  have rowsSurface :=
    TuringMachineObligationSurface_rows stateUnary tapeUnary headUnary boundUnary configurationRow
      traceRow endpointRow haltedTrace finalLedgerRow readbackUnary haltedUnary
  have finalLedgerUnary : UnaryHistory finalLedger :=
    rowsSurface.right.right.right.left
  have publicLedgerUnary : UnaryHistory publicLedger :=
    unary_cont_closed finalLedgerUnary haltedUnary publicLedgerRow
  exact
    ⟨publicLedgerUnary, rowsSurface.right.right.right.right.left,
      rowsSurface.right.right.right.right.right, publicLedgerRow⟩

theorem TuringMachinePublicCertificate_export
    {state tape head bound configuration trace readback bounded endpoint halted ledger publicSurface
      certificate : BHist}
    {haltRows : List BHist} :
    UnaryHistory state -> UnaryHistory tape -> UnaryHistory head -> UnaryHistory bound ->
      UnaryHistory halted -> Cont state tape configuration -> Cont configuration head trace ->
        Cont tape head readback -> Cont trace readback bounded -> Cont bounded bound endpoint ->
          TuringMachineHaltedTrace halted haltRows endpoint -> Cont endpoint halted ledger ->
            Cont ledger bounded publicSurface -> Cont publicSurface halted certificate ->
              UnaryHistory publicSurface ∧ UnaryHistory certificate ∧
                hsame publicSurface (append ledger bounded) ∧
                  hsame certificate (append publicSurface halted) := by
  intro stateUnary tapeUnary headUnary boundUnary haltedUnary configurationRow traceRow readbackRow
  intro boundedRow endpointRow haltedTrace ledgerRow publicSurfaceRow certificateRow
  have publicRows :=
    TuringMachineNameCertSurfaceObligation_public_surface stateUnary tapeUnary headUnary
      boundUnary haltedUnary configurationRow traceRow readbackRow boundedRow endpointRow
      haltedTrace ledgerRow publicSurfaceRow
  have publicSurfaceUnary : UnaryHistory publicSurface :=
    publicRows.right.right.right.right.right.right.left
  have certificateUnary : UnaryHistory certificate :=
    unary_cont_closed publicSurfaceUnary haltedUnary certificateRow
  exact ⟨publicSurfaceUnary, certificateUnary, publicSurfaceRow, certificateRow⟩

end BEDC.Derived.TuringMachineUp
