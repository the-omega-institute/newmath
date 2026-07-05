import BEDC.Derived.LargeModelCorpusSupplyUp.TasteGate

namespace BEDC.Derived.LargeModelCorpusSupplyUp

open BEDC.FKernel.Hist

theorem LargeModelCorpusSupplyCarrier_field_faithful_boundary
    (x : LargeModelCorpusSupplyUp) :
    exists R F W I A H K P N : BHist,
      x = LargeModelCorpusSupplyUp.mk R F W I A H K P N ∧
        largeModelCorpusSupplyFields x = [R, F, W, I, A, H, K, P, N] ∧
          List.Mem (largeModelCorpusSupplyEncodeBHist R)
            (largeModelCorpusSupplyToEventFlow x) ∧
            List.Mem (largeModelCorpusSupplyEncodeBHist F)
              (largeModelCorpusSupplyToEventFlow x) ∧
              List.Mem (largeModelCorpusSupplyEncodeBHist N)
                (largeModelCorpusSupplyToEventFlow x) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R F W I A H K P N =>
      refine ⟨R, F, W, I, A, H, K, P, N, rfl, rfl, ?_, ?_, ?_⟩
      · exact List.Mem.head _
      · exact List.Mem.tail _ (List.Mem.head _)
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _ (List.Mem.head _))))))))

end BEDC.Derived.LargeModelCorpusSupplyUp
