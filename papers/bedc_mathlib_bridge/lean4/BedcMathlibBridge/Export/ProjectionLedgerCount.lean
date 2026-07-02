import BEDC.Derived.CommonCarrierProjectionUp
import Mathlib.Data.List.Count

namespace BedcMathlibBridge.Export.ProjectionLedgerCount

abbrev BHist := BEDC.FKernel.Hist.BHist
abbrev ProjectionLedger := BEDC.Derived.CommonCarrierProjectionUp.ProjectionLedger

def projectionLedgerRowCountReadback (ledger : ProjectionLedger) (row : BHist) : Nat :=
  ledger.rowCount row

def projectionLedgerListCountSum (ledger : ProjectionLedger) (row : BHist) : Nat :=
  ledger.observed.count row +
    ledger.hidden.count row +
      ledger.scopedRows.count row +
        ledger.refused.count row +
          ledger.transport.count row +
            ledger.provenance.count row

theorem projectionLedger_rowCount_eq_list_count_sum
    (ledger : ProjectionLedger) (row : BHist) :
    projectionLedgerRowCountReadback ledger row =
      projectionLedgerListCountSum ledger row := by
  rfl

theorem projectionLedger_list_count_identity
    (ledger : ProjectionLedger) (row : BHist) :
    ledger.observed.count row = List.count row ledger.observed := by
  rfl

theorem projectionLedger_readback_apply
    (ledger : ProjectionLedger) (row : BHist) :
    projectionLedgerRowCountReadback ledger row =
      projectionLedgerRowCountReadback ledger row := by
  rfl

structure ProjectionLedgerCountExportWitness where
  readback : ProjectionLedger -> BHist -> Nat
  readback_apply : ∀ (ledger : ProjectionLedger) (row : BHist),
    readback ledger row = projectionLedgerRowCountReadback ledger row
  list_count_sum_apply : ∀ (ledger : ProjectionLedger) (row : BHist),
    readback ledger row = projectionLedgerListCountSum ledger row
  observed_list_count_apply : ∀ (ledger : ProjectionLedger) (row : BHist),
    ledger.observed.count row = List.count row ledger.observed

def projectionLedgerCountExport : ProjectionLedgerCountExportWitness where
  readback := projectionLedgerRowCountReadback
  readback_apply := projectionLedger_readback_apply
  list_count_sum_apply := projectionLedger_rowCount_eq_list_count_sum
  observed_list_count_apply := projectionLedger_list_count_identity

end BedcMathlibBridge.Export.ProjectionLedgerCount
