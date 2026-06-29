import BEDC.Derived.SupplySocketLedgerUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SupplySocketLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem SupplySocketLedgerUp_StdBridge
    {gapTag supplyKind socketSite auditGate consumptionRoute provenance nameCert : BHist} :
    Cont gapTag supplyKind consumptionRoute →
      supplySocketLedgerFromEventFlow
          (supplySocketLedgerToEventFlow
            (SupplySocketLedgerUp.mk gapTag supplyKind socketSite auditGate consumptionRoute
              provenance nameCert)) =
        some
          (SupplySocketLedgerUp.mk gapTag supplyKind socketSite auditGate consumptionRoute
            provenance nameCert) ∧
        Nonempty (BHistCarrier SupplySocketLedgerUp) ∧
          Nonempty (ChapterTasteGate SupplySocketLedgerUp) ∧
            Cont gapTag supplyKind consumptionRoute := by
  -- BEDC touchpoint anchor: BHist Cont BHistCarrier ChapterTasteGate
  intro consumption
  constructor
  · change
      BHistCarrier.fromEventFlow
          (BHistCarrier.toEventFlow
            (SupplySocketLedgerUp.mk gapTag supplyKind socketSite auditGate consumptionRoute
              provenance nameCert)) =
        some
          (SupplySocketLedgerUp.mk gapTag supplyKind socketSite auditGate consumptionRoute
            provenance nameCert)
    exact
      ChapterTasteGate.round_trip
        (SupplySocketLedgerUp.mk gapTag supplyKind socketSite auditGate consumptionRoute
          provenance nameCert)
  · exact
      ⟨⟨supplySocketLedgerBHistCarrier⟩,
        ⟨supplySocketLedgerChapterTasteGate⟩,
        consumption⟩

end BEDC.Derived.SupplySocketLedgerUp
