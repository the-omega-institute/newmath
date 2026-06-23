import BEDC.Derived.TruthTotalReflectionUp.TasteGate

namespace BEDC.Derived.TruthTotalReflectionUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem TruthTotalReflectionRootRouteTotality (x : TruthTotalReflectionUp) :
    ∃ sentence attempt diagonal transport route provenance nameCert : BHist,
      x = TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
        nameCert ∧
        List.Mem (truthTotalReflectionEncodeBHist sentence) (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist attempt) (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist diagonal) (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist transport) (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist route) (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist provenance) (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist nameCert) (BHistCarrier.toEventFlow x) ∧
        hsame attempt attempt ∧ hsame diagonal diagonal ∧ hsame transport transport ∧
          hsame route route := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier hsame
  cases x with
  | mk sentence attempt diagonal transport route provenance nameCert =>
      have sentenceRow : List.Mem (truthTotalReflectionEncodeBHist sentence)
          (BHistCarrier.toEventFlow
            (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
              nameCert)) :=
        List.Mem.tail _ (List.Mem.head _)
      have attemptRow : List.Mem (truthTotalReflectionEncodeBHist attempt)
          (BHistCarrier.toEventFlow
            (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
              nameCert)) :=
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have diagonalRow : List.Mem (truthTotalReflectionEncodeBHist diagonal)
          (BHistCarrier.toEventFlow
            (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
              nameCert)) :=
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
      have transportRow : List.Mem (truthTotalReflectionEncodeBHist transport)
          (BHistCarrier.toEventFlow
            (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
              nameCert)) :=
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
      have routeRow : List.Mem (truthTotalReflectionEncodeBHist route)
          (BHistCarrier.toEventFlow
            (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
              nameCert)) :=
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.head _)))))))))
      have provenanceRow : List.Mem (truthTotalReflectionEncodeBHist provenance)
          (BHistCarrier.toEventFlow
            (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
              nameCert)) :=
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
      have nameRow : List.Mem (truthTotalReflectionEncodeBHist nameCert)
          (BHistCarrier.toEventFlow
            (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
              nameCert)) :=
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.head _)))))))))))))
      exact
        ⟨sentence, attempt, diagonal, transport, route, provenance, nameCert, rfl,
          sentenceRow, attemptRow, diagonalRow, transportRow, routeRow, provenanceRow,
          nameRow, hsame_refl attempt, hsame_refl diagonal, hsame_refl transport,
          hsame_refl route⟩

end BEDC.Derived.TruthTotalReflectionUp
