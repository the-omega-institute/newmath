import BEDC.Derived.CommonCarrierProjectionUp
import Mathlib.Data.List.Count

namespace BedcMathlibBridge.Export.ProjectionLedgerCount

def projectionLedgerRowCountReadback
    (ledger : BEDC.Derived.CommonCarrierProjectionUp.ProjectionLedger)
    (row : BEDC.FKernel.Hist.BHist) : Nat :=
  ledger.rowCount row

def projectionLedgerListCountSum
    (ledger : BEDC.Derived.CommonCarrierProjectionUp.ProjectionLedger)
    (row : BEDC.FKernel.Hist.BHist) : Nat :=
  ledger.observed.count row +
    ledger.hidden.count row +
      ledger.scopedRows.count row +
        ledger.refused.count row +
          ledger.transport.count row +
            ledger.provenance.count row

theorem projectionLedger_rowCount_eq_list_count_sum
    (ledger : BEDC.Derived.CommonCarrierProjectionUp.ProjectionLedger)
    (row : BEDC.FKernel.Hist.BHist) :
    projectionLedgerRowCountReadback ledger row =
      List.count row ledger.observed +
        List.count row ledger.hidden +
          List.count row ledger.scopedRows +
            List.count row ledger.refused +
              List.count row ledger.transport +
                List.count row ledger.provenance := by
  rfl

theorem projectionLedger_list_count_identity
    (ledger : BEDC.Derived.CommonCarrierProjectionUp.ProjectionLedger)
    (row : BEDC.FKernel.Hist.BHist) :
    ledger.observed.count row = List.count row ledger.observed := by
  rfl

theorem projectionLedger_readback_apply
    (ledger : BEDC.Derived.CommonCarrierProjectionUp.ProjectionLedger)
    (row : BEDC.FKernel.Hist.BHist) :
    projectionLedgerRowCountReadback ledger row =
      projectionLedgerRowCountReadback ledger row := by
  rfl

structure ProjectionLedgerCountExportWitness where
  readback :
    BEDC.Derived.CommonCarrierProjectionUp.ProjectionLedger ->
      BEDC.FKernel.Hist.BHist -> Nat
  mathlib_count :
    BEDC.Derived.CommonCarrierProjectionUp.ProjectionLedger ->
      BEDC.FKernel.Hist.BHist -> Nat
  readback_apply :
    ∀ (ledger : BEDC.Derived.CommonCarrierProjectionUp.ProjectionLedger)
      (row : BEDC.FKernel.Hist.BHist),
    readback ledger row = projectionLedgerRowCountReadback ledger row
  mathlib_count_apply :
    ∀ (ledger : BEDC.Derived.CommonCarrierProjectionUp.ProjectionLedger)
      (row : BEDC.FKernel.Hist.BHist),
    mathlib_count ledger row = List.count row ledger.observed
  list_count_sum_apply :
    ∀ (ledger : BEDC.Derived.CommonCarrierProjectionUp.ProjectionLedger)
      (row : BEDC.FKernel.Hist.BHist),
    readback ledger row = projectionLedgerListCountSum ledger row
  observed_list_count_apply :
    ∀ (ledger : BEDC.Derived.CommonCarrierProjectionUp.ProjectionLedger)
      (row : BEDC.FKernel.Hist.BHist),
    ledger.observed.count row = List.count row ledger.observed

def projectionLedgerCountExport : ProjectionLedgerCountExportWitness where
  readback := projectionLedgerRowCountReadback
  mathlib_count := fun ledger row => List.count row ledger.observed
  readback_apply := projectionLedger_readback_apply
  mathlib_count_apply := by
    intro ledger row
    rfl
  list_count_sum_apply := projectionLedger_rowCount_eq_list_count_sum
  observed_list_count_apply := projectionLedger_list_count_identity

end BedcMathlibBridge.Export.ProjectionLedgerCount
