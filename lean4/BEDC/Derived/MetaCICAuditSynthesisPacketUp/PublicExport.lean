import BEDC.Derived.MetaCICAuditSynthesisPacketUp.TasteGate

namespace BEDC.Derived.MetaCICAuditSynthesisPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem MetaCICAuditSynthesisPublicExport (x : MetaCICAuditSynthesisPacketUp) :
    ∃ S C N U D A B H R P L : BHist,
      x = MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L ∧
        List.Mem (metaCICAuditSynthesisPacketEncodeBHist S) (BHistCarrier.toEventFlow x) ∧
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist C) (BHistCarrier.toEventFlow x) ∧
            List.Mem (metaCICAuditSynthesisPacketEncodeBHist N) (BHistCarrier.toEventFlow x) ∧
              List.Mem (metaCICAuditSynthesisPacketEncodeBHist U) (BHistCarrier.toEventFlow x) ∧
                List.Mem (metaCICAuditSynthesisPacketEncodeBHist D)
                  (BHistCarrier.toEventFlow x) ∧
                  List.Mem (metaCICAuditSynthesisPacketEncodeBHist A)
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
                              List.Mem BMark.b0
                                (metaCICAuditSynthesisPacketEncodeBHist
                                  (BHist.e0 BHist.Empty)) ∧
                                hsame S S ∧ hsame B B ∧ hsame L L := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier hsame
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
      · constructor
        · exact List.Mem.head _
        · constructor
          · exact List.Mem.tail _ (List.Mem.head _)
          · constructor
            · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
            · constructor
              · exact
                  List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _ (List.Mem.head _)))
              · constructor
                · exact
                    List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _ (List.Mem.head _))))
                · constructor
                  · exact
                      List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _ (List.Mem.head _)))))
                  · constructor
                    · exact
                        List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _
                                  (List.Mem.tail _ (List.Mem.head _))))))
                    · constructor
                      · exact
                          List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _
                                  (List.Mem.tail _
                                    (List.Mem.tail _
                                      (List.Mem.tail _ (List.Mem.head _)))))))
                      · constructor
                        · exact
                            List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _
                                  (List.Mem.tail _
                                    (List.Mem.tail _
                                      (List.Mem.tail _
                                        (List.Mem.tail _
                                          (List.Mem.tail _ (List.Mem.head _))))))))
                        · constructor
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
                          · constructor
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
                                                    (List.Mem.head _))))))))))
                            · constructor
                              · exact List.Mem.head _
                              · exact ⟨hsame_refl S, hsame_refl B, hsame_refl L⟩

end BEDC.Derived.MetaCICAuditSynthesisPacketUp
