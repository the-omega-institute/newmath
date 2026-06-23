import BEDC.Derived.TruthTotalReflectionUp.TasteGate

namespace BEDC.Derived.TruthTotalReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem TruthTotalReflectionDiagonalObstructionExactness (x : TruthTotalReflectionUp) :
    ∃ sentence attempt diagonal transport route provenance nameCert : BHist,
      x = TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance nameCert ∧
        hsame diagonal diagonal ∧
          hsame attempt attempt ∧
            List.Mem [BMark.b1, BMark.b1, BMark.b0] (BHistCarrier.toEventFlow x) ∧
              List.Mem (truthTotalReflectionEncodeBHist attempt)
                (BHistCarrier.toEventFlow x) ∧
                List.Mem (truthTotalReflectionEncodeBHist diagonal)
                  (BHistCarrier.toEventFlow x) := by
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
      have diagonalTagMem :
          List.Mem [BMark.b1, BMark.b1, BMark.b0]
            (BHistCarrier.toEventFlow
              (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
                nameCert)) := by
        change
          List.Mem [BMark.b1, BMark.b1, BMark.b0]
            (truthTotalReflectionToEventFlow
              (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
                nameCert))
        dsimp [truthTotalReflectionToEventFlow]
        apply List.Mem.tail
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
          hsame_refl diagonal, hsame_refl attempt, diagonalTagMem, attemptMem, diagonalMem⟩

end BEDC.Derived.TruthTotalReflectionUp
