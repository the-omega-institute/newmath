import BEDC.Derived.BishopFanModulusUp.TasteGate

namespace BEDC.Derived.BishopFanModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate
open BEDC.Derived.BishopFanModulusUp.TasteGate

theorem BishopFanModulusNonescape (x : BishopFanModulusUp) :
    ∃ F A B S Q D R U H C P N : BHist,
      x = BishopFanModulusUp.mk F A B S Q D R U H C P N ∧
        List.Mem (bishopFanModulusEncodeBHist F) (BHistCarrier.toEventFlow x) ∧
          List.Mem (bishopFanModulusEncodeBHist U) (BHistCarrier.toEventFlow x) ∧
            List.Mem (bishopFanModulusEncodeBHist N) (BHistCarrier.toEventFlow x) ∧
              List.Mem BMark.b0
                (bishopFanModulusEncodeBHist (BHist.e0 BHist.Empty)) ∧
                hsame F F ∧ hsame U U ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier hsame
  cases x with
  | mk F A B S Q D R U H C P N =>
      exists F
      exists A
      exists B
      exists S
      exists Q
      exists D
      exists R
      exists U
      exists H
      exists C
      exists P
      exists N
      constructor
      · rfl
      constructor
      · exact List.Mem.head _
      constructor
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
      constructor
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _ (List.Mem.head _)))))))))))
      constructor
      · exact List.Mem.head _
      · exact ⟨hsame_refl F, hsame_refl U, hsame_refl N⟩

end BEDC.Derived.BishopFanModulusUp
