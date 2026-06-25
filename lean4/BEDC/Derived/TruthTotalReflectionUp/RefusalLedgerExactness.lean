import BEDC.Derived.TruthTotalReflectionUp.TasteGate

namespace BEDC.Derived.TruthTotalReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem TruthTotalReflectionRefusalLedgerExactness (x : TruthTotalReflectionUp) :
    ∃ sentence attempt diagonal transport route provenance nameCert : BHist,
      x = TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
          nameCert ∧
        hsame attempt attempt ∧
          hsame diagonal diagonal ∧
            List.Mem (truthTotalReflectionEncodeBHist attempt) (BHistCarrier.toEventFlow x) ∧
              List.Mem (truthTotalReflectionEncodeBHist diagonal) (BHistCarrier.toEventFlow x) ∧
                List.Mem BMark.b1
                  (truthTotalReflectionEncodeBHist (BHist.e1 BHist.Empty)) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier hsame
  cases x with
  | mk sentence attempt diagonal transport route provenance nameCert =>
      have attemptMem :
          List.Mem (truthTotalReflectionEncodeBHist attempt)
            (BHistCarrier.toEventFlow
              (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
                nameCert)) := by
        change
          List.Mem (truthTotalReflectionEncodeBHist attempt)
            (truthTotalReflectionToEventFlow
              (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
                nameCert))
        dsimp [truthTotalReflectionToEventFlow]
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        exact List.Mem.head _
      have diagonalMem :
          List.Mem (truthTotalReflectionEncodeBHist diagonal)
            (BHistCarrier.toEventFlow
              (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
                nameCert)) := by
        change
          List.Mem (truthTotalReflectionEncodeBHist diagonal)
            (truthTotalReflectionToEventFlow
              (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
                nameCert))
        dsimp [truthTotalReflectionToEventFlow]
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        exact List.Mem.head _
      exact
        ⟨sentence, attempt, diagonal, transport, route, provenance, nameCert, rfl,
          hsame_refl attempt, hsame_refl diagonal, attemptMem, diagonalMem,
          List.Mem.head _⟩

end BEDC.Derived.TruthTotalReflectionUp
