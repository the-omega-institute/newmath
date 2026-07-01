import BEDC.Derived.GroundCompilerAuditPacketUp.TasteGate

namespace BEDC.Derived.GroundCompilerAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
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

theorem GroundCompilerAuditPacketObligationClosure (x : GroundCompilerAuditPacketUp) :
    ∃ E S R C Q M B X H T P N : BHist,
      x = GroundCompilerAuditPacketUp.mk E S R C Q M B X H T P N ∧
        groundCompilerAuditPacketToEventFlow x =
          [[BMark.b0],
            groundCompilerAuditPacketEncodeBHist E,
            [BMark.b1, BMark.b0],
            groundCompilerAuditPacketEncodeBHist S,
            [BMark.b1, BMark.b1, BMark.b0],
            groundCompilerAuditPacketEncodeBHist R,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            groundCompilerAuditPacketEncodeBHist C,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            groundCompilerAuditPacketEncodeBHist Q,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            groundCompilerAuditPacketEncodeBHist M,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            groundCompilerAuditPacketEncodeBHist B,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0],
            groundCompilerAuditPacketEncodeBHist X,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b0],
            groundCompilerAuditPacketEncodeBHist H,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            groundCompilerAuditPacketEncodeBHist T,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            groundCompilerAuditPacketEncodeBHist P,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            groundCompilerAuditPacketEncodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk E S R C Q M B X H T P N =>
      exact ⟨E, S, R, C, Q, M, B, X, H, T, P, N, rfl, rfl⟩

end BEDC.Derived.GroundCompilerAuditPacketUp
