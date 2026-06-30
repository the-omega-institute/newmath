import BEDC.Derived.TranscendentalSupplyLedgerUp.TasteGate

namespace BEDC.Derived.TranscendentalSupplyLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem TranscendentalSupplyLedger_taxonomy_exhaustion :
    Nonempty (ChapterTasteGate TranscendentalSupplyLedgerUp) ∧
      (∀ x : TranscendentalSupplyLedgerUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
        (∀ x : TranscendentalSupplyLedgerUp,
          ∃ S R T G H C P N : BHist,
            x = TranscendentalSupplyLedgerUp.mk S R T G H C P N ∧
              BHistCarrier.toEventFlow x =
                [[BMark.b0], transcendentalSupplyLedgerEncodeBHist S,
                  [BMark.b1, BMark.b0], transcendentalSupplyLedgerEncodeBHist R,
                  [BMark.b1, BMark.b1, BMark.b0],
                  transcendentalSupplyLedgerEncodeBHist T,
                  [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
                  transcendentalSupplyLedgerEncodeBHist G,
                  [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
                  transcendentalSupplyLedgerEncodeBHist H,
                  [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
                  transcendentalSupplyLedgerEncodeBHist C,
                  [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                    BMark.b0],
                  transcendentalSupplyLedgerEncodeBHist P,
                  [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                    BMark.b1, BMark.b0],
                  transcendentalSupplyLedgerEncodeBHist N]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨⟨transcendentalSupplyLedgerChapterTasteGate⟩,
      by
        intro x
        exact ChapterTasteGate.round_trip x,
      by
        intro x
        cases x with
        | mk S R T G H C P N =>
            exact ⟨S, R, T, G, H, C, P, N, rfl, rfl⟩⟩

end BEDC.Derived.TranscendentalSupplyLedgerUp
