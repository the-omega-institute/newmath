import BEDC.Derived.MetaCICAuditSynthesisPacketUp.TasteGate

namespace BEDC.Derived.MetaCICAuditSynthesisPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem MetaCICAuditSynthesisPositiveBlockerUnion
    (x : MetaCICAuditSynthesisPacketUp) :
    ∃ S C N U D A B H R P L : BHist,
      x = MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L ∧
        List.Mem (metaCICAuditSynthesisPacketEncodeBHist S)
          (BHistCarrier.toEventFlow x) ∧
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist C)
            (BHistCarrier.toEventFlow x) ∧
            List.Mem (metaCICAuditSynthesisPacketEncodeBHist N)
              (BHistCarrier.toEventFlow x) ∧
              List.Mem (metaCICAuditSynthesisPacketEncodeBHist U)
                (BHistCarrier.toEventFlow x) ∧
                List.Mem (metaCICAuditSynthesisPacketEncodeBHist D)
                  (BHistCarrier.toEventFlow x) ∧
                  List.Mem (metaCICAuditSynthesisPacketEncodeBHist A)
                    (BHistCarrier.toEventFlow x) ∧
                    List.Mem (metaCICAuditSynthesisPacketEncodeBHist B)
                      (BHistCarrier.toEventFlow x) ∧
                      List.Mem BMark.b0
                        (metaCICAuditSynthesisPacketEncodeBHist (BHist.e0 BHist.Empty)) ∧
                        hsame S S ∧ hsame B B ∧ hsame H H ∧ hsame R R ∧
                          hsame P P ∧ hsame L L := by
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
                    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              · constructor
                · exact
                    List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
                · constructor
                  · exact
                      List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
                  · constructor
                    · exact
                        List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
                    · constructor
                      · exact List.Mem.head _
                      · exact
                          ⟨hsame_refl S, hsame_refl B, hsame_refl H, hsame_refl R,
                            hsame_refl P, hsame_refl L⟩

theorem MetaCICAuditSynthesisSubstitutionBlockerExhaustion
    (x : MetaCICAuditSynthesisPacketUp) :
    ∃ S C N U D A B H R P L : BHist,
      x = MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L ∧
        List.Mem (metaCICAuditSynthesisPacketEncodeBHist U)
          (BHistCarrier.toEventFlow x) ∧
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist C)
            (BHistCarrier.toEventFlow x) ∧
            List.Mem (metaCICAuditSynthesisPacketEncodeBHist N)
              (BHistCarrier.toEventFlow x) ∧
              List.Mem (metaCICAuditSynthesisPacketEncodeBHist D)
                (BHistCarrier.toEventFlow x) ∧
                List.Mem (metaCICAuditSynthesisPacketEncodeBHist A)
                  (BHistCarrier.toEventFlow x) ∧
                  List.Mem (metaCICAuditSynthesisPacketEncodeBHist S)
                    (BHistCarrier.toEventFlow x) ∧
                    List.Mem (metaCICAuditSynthesisPacketEncodeBHist B)
                      (BHistCarrier.toEventFlow x) ∧
                      List.Mem BMark.b0
                        (metaCICAuditSynthesisPacketEncodeBHist (BHist.e0 BHist.Empty)) ∧
                        hsame U U ∧ hsame C C ∧ hsame N N ∧ hsame D D ∧
                          hsame A A ∧ hsame S S ∧ hsame B B := by
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
        · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        · constructor
          · exact List.Mem.tail _ (List.Mem.head _)
          · constructor
            · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
            · constructor
              · exact
                  List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              · constructor
                · exact
                    List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
                · constructor
                  · exact List.Mem.head _
                  · constructor
                    · exact
                        List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
                    · constructor
                      · exact List.Mem.head _
                      · exact
                          ⟨hsame_refl U, hsame_refl C, hsame_refl N, hsame_refl D,
                            hsame_refl A, hsame_refl S, hsame_refl B⟩

end BEDC.Derived.MetaCICAuditSynthesisPacketUp
