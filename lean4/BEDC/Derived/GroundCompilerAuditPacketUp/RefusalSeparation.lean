import BEDC.Derived.GroundCompilerAuditPacketUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.GroundCompilerAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.Meta.TasteGate

theorem GroundCompilerAuditPacketRefusalSeparation (x : GroundCompilerAuditPacketUp) :
    ∃ S R Q B X H T P N : BHist,
      SemanticNameCert
          (fun row : BHist =>
            hsame row Q ∨ hsame row R ∨ hsame row B ∨ hsame row S ∨ hsame row X)
          (fun row : BHist =>
            hsame row Q ∨ hsame row R ∨ hsame row B ∨ hsame row S ∨ hsame row X ∨
              hsame row H ∨ hsame row T ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            hsame row Q ∨ hsame row R ∨ hsame row B ∨ hsame row S ∨ hsame row X ∨
              hsame row H ∨ hsame row T ∨ hsame row P ∨ hsame row N)
          hsame ∧
        List.Mem (groundCompilerAuditPacketEncodeBHist Q) (BHistCarrier.toEventFlow x) ∧
          List.Mem (groundCompilerAuditPacketEncodeBHist B) (BHistCarrier.toEventFlow x) ∧
            groundCompilerAuditPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark hsame SemanticNameCert BHistCarrier
  cases x with
  | mk E S R C Q M B X H T P N =>
      let carrier : BHist → Prop := fun row : BHist =>
        hsame row Q ∨ hsame row R ∨ hsame row B ∨ hsame row S ∨ hsame row X
      let boundary : BHist → Prop := fun row : BHist =>
        hsame row Q ∨ hsame row R ∨ hsame row B ∨ hsame row S ∨ hsame row X ∨
          hsame row H ∨ hsame row T ∨ hsame row P ∨ hsame row N
      have carrierNonempty : ∃ row : BHist, carrier row :=
        ⟨Q, Or.inl (hsame_refl Q)⟩
      have carrierRespects :
          ∀ row other : BHist, hsame row other -> carrier row -> carrier other := by
        intro row other sameRows source
        cases source with
        | inl rowQ =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowQ)
        | inr tail =>
            cases tail with
            | inl rowR =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowR))
            | inr tail =>
                cases tail with
                | inl rowB =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowB)))
                | inr tail =>
                    cases tail with
                    | inl rowS =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowS))))
                    | inr rowX =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (hsame_trans (hsame_symm sameRows) rowX))))
      have carrierToBoundary : ∀ row : BHist, carrier row -> boundary row := by
        intro row source
        cases source with
        | inl rowQ =>
            exact Or.inl rowQ
        | inr tail =>
            cases tail with
            | inl rowR =>
                exact Or.inr (Or.inl rowR)
            | inr tail =>
                cases tail with
                | inl rowB =>
                    exact Or.inr (Or.inr (Or.inl rowB))
                | inr tail =>
                    cases tail with
                    | inl rowS =>
                        exact Or.inr (Or.inr (Or.inr (Or.inl rowS)))
                    | inr rowX =>
                        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rowX))))
      have cert :
          SemanticNameCert carrier boundary boundary hsame := {
        core := {
          carrier_inhabited := carrierNonempty
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
            intro row other sameRows source
            exact carrierRespects row other sameRows source
        }
        pattern_sound := by
          intro row source
          exact carrierToBoundary row source
        ledger_sound := by
          intro row source
          exact carrierToBoundary row source
      }
      refine ⟨S, R, Q, B, X, H, T, P, N, cert, ?_, ?_, rfl⟩
      · simp only [BHistCarrier.toEventFlow, groundCompilerAuditPacketToEventFlow]
        repeat' constructor
      · simp only [BHistCarrier.toEventFlow, groundCompilerAuditPacketToEventFlow]
        repeat' constructor

end BEDC.Derived.GroundCompilerAuditPacketUp
