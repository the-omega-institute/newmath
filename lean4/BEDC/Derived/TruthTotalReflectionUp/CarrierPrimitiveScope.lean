import BEDC.Derived.TruthTotalReflectionUp.TasteGate

namespace BEDC.Derived.TruthTotalReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem TruthTotalReflectionCarrierPrimitiveScope (x : TruthTotalReflectionUp) :
    ∃ sentence attempt diagonal transport route provenance nameCert : BHist,
      x = TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
        nameCert ∧
        List.Mem [BMark.b0] (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist sentence) (BHistCarrier.toEventFlow x) ∧
        List.Mem [BMark.b1, BMark.b0] (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist attempt) (BHistCarrier.toEventFlow x) ∧
        List.Mem [BMark.b1, BMark.b1, BMark.b0] (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist diagonal) (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist transport) (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist route) (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist provenance) (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist nameCert) (BHistCarrier.toEventFlow x) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier
  cases x with
  | mk sentence attempt diagonal transport route provenance nameCert =>
      have tagSentence : List.Mem [BMark.b0]
          (BHistCarrier.toEventFlow
            (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
              nameCert)) :=
        List.Mem.head _
      have sentenceRow : List.Mem (truthTotalReflectionEncodeBHist sentence)
          (BHistCarrier.toEventFlow
            (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
              nameCert)) :=
        List.Mem.tail _ (List.Mem.head _)
      have tagAttempt : List.Mem [BMark.b1, BMark.b0]
          (BHistCarrier.toEventFlow
            (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
              nameCert)) :=
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      have attemptRow : List.Mem (truthTotalReflectionEncodeBHist attempt)
          (BHistCarrier.toEventFlow
            (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
              nameCert)) :=
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have tagDiagonal : List.Mem [BMark.b1, BMark.b1, BMark.b0]
          (BHistCarrier.toEventFlow
            (TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
              nameCert)) :=
        List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
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
          tagSentence, sentenceRow, tagAttempt, attemptRow, tagDiagonal, diagonalRow,
          transportRow, routeRow, provenanceRow, nameRow⟩

end BEDC.Derived.TruthTotalReflectionUp
