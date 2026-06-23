import BEDC.Derived.TruthTotalReflectionUp.TasteGate

namespace BEDC.Derived.TruthTotalReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem TruthTotalReflectionLedgerNonescape (x : TruthTotalReflectionUp) :
    ∃ sentence attempt diagonal transport route provenance nameCert : BHist,
      x = TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
          nameCert ∧
        hsame provenance provenance ∧
          hsame nameCert nameCert ∧
            List.Mem (truthTotalReflectionEncodeBHist provenance)
              (BHistCarrier.toEventFlow x) ∧
              List.Mem (truthTotalReflectionEncodeBHist nameCert)
                (BHistCarrier.toEventFlow x) ∧
                List.Mem BMark.b0
                  (truthTotalReflectionEncodeBHist (BHist.e0 BHist.Empty)) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier hsame
  cases x with
  | mk sentence attempt diagonal transport route provenance nameCert =>
      have provenanceMem :
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
      have nameCertMem :
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
          hsame_refl provenance, hsame_refl nameCert, provenanceMem, nameCertMem,
          List.Mem.head _⟩

end BEDC.Derived.TruthTotalReflectionUp
