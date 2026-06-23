import BEDC.Derived.TruthTotalReflectionUp.TasteGate

namespace BEDC.Derived.TruthTotalReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem TruthTotalReflectionDiagonalRouteScope (x : TruthTotalReflectionUp) :
    ∃ sentence attempt diagonal transport route provenance nameCert : BHist,
      x = TruthTotalReflectionUp.mk sentence attempt diagonal transport route provenance
        nameCert ∧
        List.Mem [BMark.b1, BMark.b1, BMark.b0] (BHistCarrier.toEventFlow x) ∧
        List.Mem [BMark.b1, BMark.b1, BMark.b1, BMark.b0]
          (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist diagonal) (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist transport) (BHistCarrier.toEventFlow x) ∧
        List.Mem (truthTotalReflectionEncodeBHist route) (BHistCarrier.toEventFlow x) ∧
        hsame attempt attempt ∧ hsame diagonal diagonal ∧ hsame transport transport ∧
          hsame route route := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier hsame
  cases x with
  | mk sentence attempt diagonal transport route provenance nameCert =>
      exact
        ⟨sentence, attempt, diagonal, transport, route, provenance, nameCert, rfl,
          List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.head _))))))))),
          hsame_refl attempt, hsame_refl diagonal, hsame_refl transport,
          hsame_refl route⟩

end BEDC.Derived.TruthTotalReflectionUp
