import BEDC.Derived.TruthTotalReflectionUp.TasteGate

namespace BEDC.Derived.TruthTotalReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem TruthTotalReflectionDownstreamBoundaryPackage (x : TruthTotalReflectionUp) :
    ∃ sentence attempt diagonal transport route provenance nameCert : BHist,
      x = TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
          nameCert ∧
        List.Mem [BMark.b0] (BHistCarrier.toEventFlow x) ∧
          List.Mem [BMark.b1, BMark.b0] (BHistCarrier.toEventFlow x) ∧
            List.Mem [BMark.b1, BMark.b1, BMark.b0] (BHistCarrier.toEventFlow x) ∧
              List.Mem (truthTotalReflectionEncodeBHist sentence)
                (BHistCarrier.toEventFlow x) ∧
                List.Mem (truthTotalReflectionEncodeBHist attempt)
                  (BHistCarrier.toEventFlow x) ∧
                  List.Mem (truthTotalReflectionEncodeBHist diagonal)
                    (BHistCarrier.toEventFlow x) ∧
                    List.Mem (truthTotalReflectionEncodeBHist transport)
                      (BHistCarrier.toEventFlow x) ∧
                      List.Mem (truthTotalReflectionEncodeBHist route)
                        (BHistCarrier.toEventFlow x) ∧
                        List.Mem (truthTotalReflectionEncodeBHist provenance)
                          (BHistCarrier.toEventFlow x) ∧
                          List.Mem (truthTotalReflectionEncodeBHist nameCert)
                            (BHistCarrier.toEventFlow x) ∧
                            hsame attempt attempt ∧
                              hsame diagonal diagonal ∧
                                hsame transport transport ∧
                                  hsame route route ∧
                                    hsame provenance provenance ∧
                                      hsame nameCert nameCert := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier hsame
  cases x with
  | mk sentence attempt diagonal transport route provenance nameCert =>
      dsimp [BHistCarrier.toEventFlow, truthTotalReflectionToEventFlow]
      exact
        ⟨sentence, attempt, diagonal, transport, route, provenance, nameCert, rfl,
          List.Mem.head _,
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.head _)))),
          List.Mem.tail _ (List.Mem.head _),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.head _))))))))),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
                (List.Mem.tail _ (List.Mem.head _))))))))))))),
          hsame_refl attempt, hsame_refl diagonal, hsame_refl transport,
          hsame_refl route, hsame_refl provenance, hsame_refl nameCert⟩

end BEDC.Derived.TruthTotalReflectionUp
