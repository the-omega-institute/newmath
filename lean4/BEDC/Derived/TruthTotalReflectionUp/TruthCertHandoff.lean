import BEDC.Derived.TruthTotalReflectionUp.TasteGate

namespace BEDC.Derived.TruthTotalReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem TruthTotalReflectionTruthCertHandoff (x : TruthTotalReflectionUp) :
    ∃ sentence attempt diagonal transport route provenance nameCert : BHist,
      x = TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
        nameCert ∧
        List.Mem [BMark.b1, BMark.b0] (BHistCarrier.toEventFlow x) ∧
        List.Mem [BMark.b1, BMark.b1, BMark.b0] (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist attempt)
          (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist diagonal)
          (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist provenance)
          (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist nameCert)
          (BHistCarrier.toEventFlow x) ∧
        hsame attempt attempt ∧ hsame diagonal diagonal ∧
          hsame provenance provenance ∧ hsame nameCert nameCert := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier hsame
  cases x with
  | mk sentence attempt diagonal transport route provenance nameCert =>
      have attemptTag :
          List.Mem [BMark.b1, BMark.b0]
            (BHistCarrier.toEventFlow
              (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
                nameCert)) := by
        change
          List.Mem [BMark.b1, BMark.b0]
            (truthTotalReflectionToEventFlow
              (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
                nameCert))
        dsimp [truthTotalReflectionToEventFlow]
        apply List.Mem.tail
        apply List.Mem.tail
        exact List.Mem.head _
      have diagonalTag :
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
      have attemptRow :
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
      have diagonalRow :
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
      have provenanceRow :
          List.Mem (truthTotalReflectionEncodeBHist provenance)
            (BHistCarrier.toEventFlow
              (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
                nameCert)) := by
        change
          List.Mem (truthTotalReflectionEncodeBHist provenance)
            (truthTotalReflectionToEventFlow
              (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
                nameCert))
        dsimp [truthTotalReflectionToEventFlow]
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        exact List.Mem.head _
      have nameCertRow :
          List.Mem (truthTotalReflectionEncodeBHist nameCert)
            (BHistCarrier.toEventFlow
              (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
                nameCert)) := by
        change
          List.Mem (truthTotalReflectionEncodeBHist nameCert)
            (truthTotalReflectionToEventFlow
              (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
                nameCert))
        dsimp [truthTotalReflectionToEventFlow]
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        exact List.Mem.head _
      exact
        ⟨sentence, attempt, diagonal, transport, route, provenance, nameCert, rfl,
          attemptTag, diagonalTag, attemptRow, diagonalRow, provenanceRow, nameCertRow,
          hsame_refl attempt, hsame_refl diagonal, hsame_refl provenance,
          hsame_refl nameCert⟩

end BEDC.Derived.TruthTotalReflectionUp
