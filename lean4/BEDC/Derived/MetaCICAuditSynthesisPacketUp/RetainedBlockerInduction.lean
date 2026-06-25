import BEDC.Derived.MetaCICAuditSynthesisPacketUp.ConsistencyBlockerLedger
import BEDC.Derived.MetaCICAuditSynthesisPacketUp.CriticalPathNonescape
import BEDC.Derived.MetaCICAuditSynthesisPacketUp.PositiveBlockerUnion

namespace BEDC.Derived.MetaCICAuditSynthesisPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem MetaCICAuditSynthesisRetainedBlockerInduction :
    forall x : MetaCICAuditSynthesisPacketUp, forall rows : List BHist,
      rows = metaCICAuditSynthesisPacketFields x ->
        rows ≠ [] ->
          (∃ S C N U D A B H R P L : BHist,
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
                              (metaCICAuditSynthesisPacketEncodeBHist
                                (BHist.e0 BHist.Empty)) ∧
                              hsame S S ∧ hsame B B ∧ hsame H H ∧ hsame R R ∧
                                hsame P P ∧ hsame L L) ∧
            (∃ S C N U D A B H R P L : BHist,
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
                                (metaCICAuditSynthesisPacketEncodeBHist
                                  (BHist.e0 BHist.Empty)) ∧
                                hsame S S ∧ hsame B B) ∧
              (∃ S C N U D A B H R P L : BHist,
                x = MetaCICAuditSynthesisPacketUp.mk S C N U D A B H R P L ∧
                  List.Mem (metaCICAuditSynthesisPacketEncodeBHist S)
                    (BHistCarrier.toEventFlow x) ∧
                    List.Mem (metaCICAuditSynthesisPacketEncodeBHist B)
                      (BHistCarrier.toEventFlow x) ∧
                      hsame S S ∧ hsame B B) := by
  -- BEDC touchpoint anchor: BHist BMark hsame MetaCICAuditSynthesisPacketUp
  intro x rows rows_eq retained
  induction rows with
  | nil =>
      exact False.elim (retained rfl)
  | cons _row _tail _ih =>
      exact
        ⟨MetaCICAuditSynthesisPositiveBlockerUnion x,
          MetaCICAuditSynthesisRouteUnionExactness x,
          MetaCICAuditSynthesisConsistencyBlockerLedger x⟩

end BEDC.Derived.MetaCICAuditSynthesisPacketUp
