import BEDC.Derived.MetaCICAuditSynthesisPacketUp.TasteGate

namespace BEDC.Derived.MetaCICAuditSynthesisPacketUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem MetaCICAuditSynthesisNormalizationBlockerMonotonicity
    (x : MetaCICAuditSynthesisPacketUp) :
    ∃ S C N U D A B H R P L : BHist,
      x = MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L ∧
        List.Mem (metaCICAuditSynthesisPacketEncodeBHist N)
          (BHistCarrier.toEventFlow x) ∧
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist S)
            (BHistCarrier.toEventFlow x) ∧
            List.Mem (metaCICAuditSynthesisPacketEncodeBHist B)
              (BHistCarrier.toEventFlow x) ∧
              List.Mem (metaCICAuditSynthesisPacketEncodeBHist H)
                (BHistCarrier.toEventFlow x) ∧
                List.Mem (metaCICAuditSynthesisPacketEncodeBHist R)
                  (BHistCarrier.toEventFlow x) ∧
                  List.Mem (metaCICAuditSynthesisPacketEncodeBHist P)
                    (BHistCarrier.toEventFlow x) ∧
                    List.Mem (metaCICAuditSynthesisPacketEncodeBHist L)
                      (BHistCarrier.toEventFlow x) ∧
                      hsame N N ∧ hsame S S ∧ hsame B B ∧ hsame H H ∧ hsame R R ∧
                        hsame P P ∧ hsame L L := by
  -- BEDC touchpoint anchor: BHist BHistCarrier hsame
  cases x with
  | mk S C N U D A B H R P L =>
      exists S
      exists C
      exists N
      exists U
      exists D
      exists A
      exists B
      exists H
      exists R
      exists P
      exists L
      constructor
      · rfl
      constructor
      · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      constructor
      · exact List.Mem.head _
      constructor
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _ (List.Mem.head _))))))
      constructor
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _ (List.Mem.head _)))))))
      constructor
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _ (List.Mem.head _))))))))
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
                          (List.Mem.tail _ (List.Mem.head _)))))))))
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
                            (List.Mem.tail _ (List.Mem.head _))))))))))
      · exact
          ⟨hsame_refl N, hsame_refl S, hsame_refl B, hsame_refl H, hsame_refl R,
            hsame_refl P, hsame_refl L⟩

end BEDC.Derived.MetaCICAuditSynthesisPacketUp
