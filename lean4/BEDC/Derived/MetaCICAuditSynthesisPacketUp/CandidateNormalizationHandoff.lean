import BEDC.Derived.MetaCICAuditSynthesisPacketUp.TasteGate

namespace BEDC.Derived.MetaCICAuditSynthesisPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem MetaCICAuditSynthesisCandidateNormalizationHandoff
    (x : MetaCICAuditSynthesisPacketUp) :
    ∃ S C N U D A B H R P L : BHist,
      x = MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L ∧
        List.Mem (metaCICAuditSynthesisPacketEncodeBHist C)
          (BHistCarrier.toEventFlow x) ∧
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
                        List.Mem BMark.b0
                          (metaCICAuditSynthesisPacketEncodeBHist (BHist.e0 BHist.Empty)) ∧
                          hsame C C ∧ hsame N N ∧ hsame S S ∧ hsame B B ∧
                            hsame L L := by
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
      have memS :
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist S)
            (BHistCarrier.toEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L)) := by
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist S)
            (metaCICAuditSynthesisPacketToEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L))
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist S)
            [metaCICAuditSynthesisPacketEncodeBHist S,
              metaCICAuditSynthesisPacketEncodeBHist C,
              metaCICAuditSynthesisPacketEncodeBHist N,
              metaCICAuditSynthesisPacketEncodeBHist U,
              metaCICAuditSynthesisPacketEncodeBHist D,
              metaCICAuditSynthesisPacketEncodeBHist A,
              metaCICAuditSynthesisPacketEncodeBHist B,
              metaCICAuditSynthesisPacketEncodeBHist H,
              metaCICAuditSynthesisPacketEncodeBHist R,
              metaCICAuditSynthesisPacketEncodeBHist P,
              metaCICAuditSynthesisPacketEncodeBHist L]
        exact List.Mem.head _
      have memC :
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist C)
            (BHistCarrier.toEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L)) := by
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist C)
            (metaCICAuditSynthesisPacketToEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L))
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist C)
            [metaCICAuditSynthesisPacketEncodeBHist S,
              metaCICAuditSynthesisPacketEncodeBHist C,
              metaCICAuditSynthesisPacketEncodeBHist N,
              metaCICAuditSynthesisPacketEncodeBHist U,
              metaCICAuditSynthesisPacketEncodeBHist D,
              metaCICAuditSynthesisPacketEncodeBHist A,
              metaCICAuditSynthesisPacketEncodeBHist B,
              metaCICAuditSynthesisPacketEncodeBHist H,
              metaCICAuditSynthesisPacketEncodeBHist R,
              metaCICAuditSynthesisPacketEncodeBHist P,
              metaCICAuditSynthesisPacketEncodeBHist L]
        exact List.Mem.tail _ (List.Mem.head _)
      have memN :
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist N)
            (BHistCarrier.toEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L)) := by
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist N)
            (metaCICAuditSynthesisPacketToEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L))
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist N)
            [metaCICAuditSynthesisPacketEncodeBHist S,
              metaCICAuditSynthesisPacketEncodeBHist C,
              metaCICAuditSynthesisPacketEncodeBHist N,
              metaCICAuditSynthesisPacketEncodeBHist U,
              metaCICAuditSynthesisPacketEncodeBHist D,
              metaCICAuditSynthesisPacketEncodeBHist A,
              metaCICAuditSynthesisPacketEncodeBHist B,
              metaCICAuditSynthesisPacketEncodeBHist H,
              metaCICAuditSynthesisPacketEncodeBHist R,
              metaCICAuditSynthesisPacketEncodeBHist P,
              metaCICAuditSynthesisPacketEncodeBHist L]
        exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      have memB :
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist B)
            (BHistCarrier.toEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L)) := by
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist B)
            (metaCICAuditSynthesisPacketToEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L))
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist B)
            [metaCICAuditSynthesisPacketEncodeBHist S,
              metaCICAuditSynthesisPacketEncodeBHist C,
              metaCICAuditSynthesisPacketEncodeBHist N,
              metaCICAuditSynthesisPacketEncodeBHist U,
              metaCICAuditSynthesisPacketEncodeBHist D,
              metaCICAuditSynthesisPacketEncodeBHist A,
              metaCICAuditSynthesisPacketEncodeBHist B,
              metaCICAuditSynthesisPacketEncodeBHist H,
              metaCICAuditSynthesisPacketEncodeBHist R,
              metaCICAuditSynthesisPacketEncodeBHist P,
              metaCICAuditSynthesisPacketEncodeBHist L]
        exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _ (List.Mem.head _))))))
      have memH :
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist H)
            (BHistCarrier.toEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L)) := by
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist H)
            (metaCICAuditSynthesisPacketToEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L))
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist H)
            [metaCICAuditSynthesisPacketEncodeBHist S,
              metaCICAuditSynthesisPacketEncodeBHist C,
              metaCICAuditSynthesisPacketEncodeBHist N,
              metaCICAuditSynthesisPacketEncodeBHist U,
              metaCICAuditSynthesisPacketEncodeBHist D,
              metaCICAuditSynthesisPacketEncodeBHist A,
              metaCICAuditSynthesisPacketEncodeBHist B,
              metaCICAuditSynthesisPacketEncodeBHist H,
              metaCICAuditSynthesisPacketEncodeBHist R,
              metaCICAuditSynthesisPacketEncodeBHist P,
              metaCICAuditSynthesisPacketEncodeBHist L]
        exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _ (List.Mem.head _)))))))
      have memR :
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist R)
            (BHistCarrier.toEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L)) := by
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist R)
            (metaCICAuditSynthesisPacketToEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L))
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist R)
            [metaCICAuditSynthesisPacketEncodeBHist S,
              metaCICAuditSynthesisPacketEncodeBHist C,
              metaCICAuditSynthesisPacketEncodeBHist N,
              metaCICAuditSynthesisPacketEncodeBHist U,
              metaCICAuditSynthesisPacketEncodeBHist D,
              metaCICAuditSynthesisPacketEncodeBHist A,
              metaCICAuditSynthesisPacketEncodeBHist B,
              metaCICAuditSynthesisPacketEncodeBHist H,
              metaCICAuditSynthesisPacketEncodeBHist R,
              metaCICAuditSynthesisPacketEncodeBHist P,
              metaCICAuditSynthesisPacketEncodeBHist L]
        exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _ (List.Mem.head _))))))))
      have memP :
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist P)
            (BHistCarrier.toEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L)) := by
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist P)
            (metaCICAuditSynthesisPacketToEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L))
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist P)
            [metaCICAuditSynthesisPacketEncodeBHist S,
              metaCICAuditSynthesisPacketEncodeBHist C,
              metaCICAuditSynthesisPacketEncodeBHist N,
              metaCICAuditSynthesisPacketEncodeBHist U,
              metaCICAuditSynthesisPacketEncodeBHist D,
              metaCICAuditSynthesisPacketEncodeBHist A,
              metaCICAuditSynthesisPacketEncodeBHist B,
              metaCICAuditSynthesisPacketEncodeBHist H,
              metaCICAuditSynthesisPacketEncodeBHist R,
              metaCICAuditSynthesisPacketEncodeBHist P,
              metaCICAuditSynthesisPacketEncodeBHist L]
        exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _ (List.Mem.head _)))))))))
      have memL :
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist L)
            (BHistCarrier.toEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L)) := by
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist L)
            (metaCICAuditSynthesisPacketToEventFlow
              (MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L))
        change
          List.Mem (metaCICAuditSynthesisPacketEncodeBHist L)
            [metaCICAuditSynthesisPacketEncodeBHist S,
              metaCICAuditSynthesisPacketEncodeBHist C,
              metaCICAuditSynthesisPacketEncodeBHist N,
              metaCICAuditSynthesisPacketEncodeBHist U,
              metaCICAuditSynthesisPacketEncodeBHist D,
              metaCICAuditSynthesisPacketEncodeBHist A,
              metaCICAuditSynthesisPacketEncodeBHist B,
              metaCICAuditSynthesisPacketEncodeBHist H,
              metaCICAuditSynthesisPacketEncodeBHist R,
              metaCICAuditSynthesisPacketEncodeBHist P,
              metaCICAuditSynthesisPacketEncodeBHist L]
        exact
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
      exact
        ⟨rfl, memC, memN, memS, memB, memH, memR, memP, memL, List.Mem.head _,
          hsame_refl C, hsame_refl N, hsame_refl S, hsame_refl B, hsame_refl L⟩

end BEDC.Derived.MetaCICAuditSynthesisPacketUp
