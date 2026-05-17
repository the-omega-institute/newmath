import BEDC.Derived.GroundCompilerAuditMapUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.GroundCompilerAuditMapUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
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

theorem GroundCompilerAuditMapCarrier_report_boundary_exactness :
    (∀ x : GroundCompilerAuditMapUp,
      ∃ I K E C R Q F X H T P N : BHist,
        x = GroundCompilerAuditMapUp.mk I K E C R Q F X H T P N ∧
          FieldFaithful.fields x = [I, K, E, C, R, Q, F, X, H, T, P, N]) ∧
      (∀ I K E C R F X H T P N : BHist,
        BHistCarrier.toEventFlow
          (GroundCompilerAuditMapUp.mk I K E C R (BHist.e1 BHist.Empty) F X H T P N) ≠
        BHistCarrier.toEventFlow
          (GroundCompilerAuditMapUp.mk I K E C R BHist.Empty F X H T P N)) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · intro x
    cases x with
    | mk I K E C R Q F X H T P N =>
        exact ⟨I, K, E, C, R, Q, F, X, H, T, P, N, rfl, rfl⟩
  · intro I K E C R F X H T P N heq
    change
      groundCompilerAuditMapToEventFlow
          (GroundCompilerAuditMapUp.mk I K E C R (BHist.e1 BHist.Empty) F X H T P N) =
        groundCompilerAuditMapToEventFlow
          (GroundCompilerAuditMapUp.mk I K E C R BHist.Empty F X H T P N) at heq
    injection heq with _ htail₁
    injection htail₁ with _ htail₂
    injection htail₂ with _ htail₃
    injection htail₃ with _ htail₄
    injection htail₄ with _ htail₅
    injection htail₅ with _ htail₆
    injection htail₆ with _ htail₇
    injection htail₇ with _ htail₈
    injection htail₈ with _ htail₉
    injection htail₉ with _ htail₁₀
    injection htail₁₀ with _ htail₁₁
    injection htail₁₁ with hrow _
    cases hrow

theorem GroundCompilerAuditMapCarrier_frontier_handoff_nonescape
    {I K E C R Q F X H T P N I' K' E' C' R' Q' F' X' H' T' P' N' : BHist}
    (hflow :
      BHistCarrier.toEventFlow (GroundCompilerAuditMapUp.mk I K E C R Q F X H T P N) =
        BHistCarrier.toEventFlow (GroundCompilerAuditMapUp.mk I' K' E' C' R' Q' F' X' H' T' P' N')) :
    K = K' ∧ F = F' ∧ X = X' ∧ T = T' ∧
      groundCompilerAuditMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  have hdecode :
      ∀ h : BHist, groundCompilerAuditMapDecodeBHist
        (groundCompilerAuditMapEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  change
    groundCompilerAuditMapToEventFlow (GroundCompilerAuditMapUp.mk I K E C R Q F X H T P N) =
      groundCompilerAuditMapToEventFlow
        (GroundCompilerAuditMapUp.mk I' K' E' C' R' Q' F' X' H' T' P' N') at hflow
  have hread :
      groundCompilerAuditMapFromEventFlow
          (groundCompilerAuditMapToEventFlow (GroundCompilerAuditMapUp.mk I K E C R Q F X H T P N)) =
        groundCompilerAuditMapFromEventFlow
          (groundCompilerAuditMapToEventFlow
            (GroundCompilerAuditMapUp.mk I' K' E' C' R' Q' F' X' H' T' P' N')) :=
    congrArg groundCompilerAuditMapFromEventFlow hflow
  change
    some
        (GroundCompilerAuditMapUp.mk
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist I))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist K))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist E))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist C))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist R))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist Q))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist F))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist X))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist H))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist T))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist P))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist N))) =
      some
        (GroundCompilerAuditMapUp.mk
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist I'))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist K'))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist E'))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist C'))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist R'))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist Q'))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist F'))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist X'))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist H'))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist T'))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist P'))
          (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist N'))) at hread
  rw [hdecode I, hdecode K, hdecode E, hdecode C, hdecode R, hdecode Q, hdecode F,
    hdecode X, hdecode H, hdecode T, hdecode P, hdecode N, hdecode I', hdecode K',
    hdecode E', hdecode C', hdecode R', hdecode Q', hdecode F', hdecode X',
    hdecode H', hdecode T', hdecode P', hdecode N'] at hread
  injection hread with hpacket
  injection hpacket with _ hK _ _ _ _ hF hX _ hT _ _
  exact ⟨hK, hF, hX, hT, rfl⟩

theorem GroundCompilerAuditMapNameCert_obligations {I K E C R Q F X H T P N : BHist}
    (inventoryRoute : Cont I K T)
    (compilerRoute : Cont E C T)
    (reportRoute : Cont R Q T)
    (frontierRoute : Cont Q F T)
    (handoffRoute : Cont F X T) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row I ∧
          ∃ packet : GroundCompilerAuditMapUp,
            packet = GroundCompilerAuditMapUp.mk I K E C R Q F X H T P N)
      (fun row : BHist => hsame row I ∧ hsame K K ∧ hsame Q Q ∧ hsame F F)
      (fun row : BHist =>
        Cont I K T ∧ Cont E C T ∧ Cont R Q T ∧ Cont Q F T ∧ Cont F X T ∧
          hsame row I ∧ hsame P P ∧ hsame N N)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro I
          ⟨hsame_refl I,
            Exists.intro (GroundCompilerAuditMapUp.mk I K E C R Q F X H T P N) rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, hsame_refl K, hsame_refl Q, hsame_refl F⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨inventoryRoute, compilerRoute, reportRoute, frontierRoute, handoffRoute,
          sourceRow.left, hsame_refl P, hsame_refl N⟩
  }

end BEDC.Derived.GroundCompilerAuditMapUp
