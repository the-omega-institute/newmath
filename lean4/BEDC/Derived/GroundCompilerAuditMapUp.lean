import BEDC.Derived.GroundCompilerAuditMapUp.TasteGate

namespace BEDC.Derived.GroundCompilerAuditMapUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem GroundCompilerAuditMapCarrier_conditional_cell_preservation :
    (∀ x : GroundCompilerAuditMapUp,
      ∃ I K E C R Q F X H T P N : BHist,
        x = GroundCompilerAuditMapUp.mk I K E C R Q F X H T P N ∧
          FieldFaithful.fields x = [I, K, E, C, R, Q, F, X, H, T, P, N]) ∧
      (∀ I E C R Q F X H T P N : BHist,
        BHistCarrier.toEventFlow
          (GroundCompilerAuditMapUp.mk I (BHist.e0 BHist.Empty) E C R Q F X H T P N) ≠
        BHistCarrier.toEventFlow
          (GroundCompilerAuditMapUp.mk I BHist.Empty E C R Q F X H T P N)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    cases x with
    | mk I K E C R Q F X H T P N =>
        exact ⟨I, K, E, C, R, Q, F, X, H, T, P, N, rfl, rfl⟩
  · intro I E C R Q F X H T P N heq
    change
      groundCompilerAuditMapToEventFlow
          (GroundCompilerAuditMapUp.mk I (BHist.e0 BHist.Empty) E C R Q F X H T P N) =
        groundCompilerAuditMapToEventFlow
          (GroundCompilerAuditMapUp.mk I BHist.Empty E C R Q F X H T P N) at heq
    injection heq with _ htail₁
    injection htail₁ with _ htail₂
    injection htail₂ with _ htail₃
    injection htail₃ with hrow _
    cases hrow

end BEDC.Derived.GroundCompilerAuditMapUp
