import BEDC.Derived.GroundCompilerAuditPacketUp.TasteGate

namespace BEDC.Derived.GroundCompilerAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem GroundCompilerAuditPacketNameCertObligations (x : GroundCompilerAuditPacketUp) :
    ∃ E S R C Q M B X H T P N : BHist,
      x = GroundCompilerAuditPacketUp.mk E S R C Q M B X H T P N ∧
        List.Mem (groundCompilerAuditPacketEncodeBHist E) (BHistCarrier.toEventFlow x) ∧
        List.Mem (groundCompilerAuditPacketEncodeBHist S) (BHistCarrier.toEventFlow x) ∧
        List.Mem (groundCompilerAuditPacketEncodeBHist R) (BHistCarrier.toEventFlow x) ∧
        List.Mem (groundCompilerAuditPacketEncodeBHist C) (BHistCarrier.toEventFlow x) ∧
        List.Mem (groundCompilerAuditPacketEncodeBHist Q) (BHistCarrier.toEventFlow x) ∧
        List.Mem (groundCompilerAuditPacketEncodeBHist M) (BHistCarrier.toEventFlow x) ∧
        List.Mem (groundCompilerAuditPacketEncodeBHist B) (BHistCarrier.toEventFlow x) ∧
        List.Mem (groundCompilerAuditPacketEncodeBHist X) (BHistCarrier.toEventFlow x) ∧
        hsame H H ∧ hsame T T ∧ hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist hsame BHistCarrier
  cases x with
  | mk E S R C Q M B X H T P N =>
      refine ⟨E, S, R, C, Q, M, B, X, H, T, P, N, rfl, ?_⟩
      simp only [BHistCarrier.toEventFlow, groundCompilerAuditPacketToEventFlow]
      repeat' constructor

end BEDC.Derived.GroundCompilerAuditPacketUp
