import BEDC.Derived.GroundCompilerAuditPacketUp.TasteGate

namespace BEDC.Derived.GroundCompilerAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem GroundCompilerAuditPacketQueryReplay (x : GroundCompilerAuditPacketUp) :
    ∃ B Q M T P N : BHist,
      List.Mem (groundCompilerAuditPacketEncodeBHist B) (BHistCarrier.toEventFlow x) ∧
        List.Mem (groundCompilerAuditPacketEncodeBHist Q) (BHistCarrier.toEventFlow x) ∧
        List.Mem (groundCompilerAuditPacketEncodeBHist M) (BHistCarrier.toEventFlow x) ∧
        hsame T T ∧ hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist hsame BHistCarrier
  cases x with
  | mk E S R C Q M B X H T P N =>
      refine ⟨B, Q, M, T, P, N, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [BHistCarrier.toEventFlow, groundCompilerAuditPacketToEventFlow]
        repeat' constructor
      · simp only [BHistCarrier.toEventFlow, groundCompilerAuditPacketToEventFlow]
        repeat' constructor
      · simp only [BHistCarrier.toEventFlow, groundCompilerAuditPacketToEventFlow]
        repeat' constructor
      · exact hsame_refl T
      · exact hsame_refl P
      · exact hsame_refl N

end BEDC.Derived.GroundCompilerAuditPacketUp
