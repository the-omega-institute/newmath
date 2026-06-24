import BEDC.Derived.VerificationFailureRoadmapUp.TasteGate

namespace BEDC.Derived.VerificationFailureRoadmapUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem VerificationFailureRoadmapDowngradeRoute
    (R A F D M U B T C P N : BHist) :
    verificationFailureRoadmapFields
          (VerificationFailureRoadmapUp.mk R A F D M U B T C P N) =
        [R, A, F, D, M, U, B, T, C, P, N] ∧
      Cont A F (append A F) ∧
        Cont F D (append F D) ∧
          SemanticNameCert
            (fun h : BHist => hsame h (append F D))
            (fun h : BHist =>
              hsame h A ∨ hsame h F ∨ hsame h D ∨ hsame h (append F D))
            (fun h : BHist =>
              hsame h (append F D) ∧ Cont A F (append A F) ∧
                Cont F D (append F D))
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have cert :
      SemanticNameCert
        (fun h : BHist => hsame h (append F D))
        (fun h : BHist =>
          hsame h A ∨ hsame h F ∨ hsame h D ∨ hsame h (append F D))
        (fun h : BHist =>
          hsame h (append F D) ∧ Cont A F (append A F) ∧
            Cont F D (append F D))
        hsame := {
    core := {
      carrier_inhabited := Exists.intro (append F D) (hsame_refl (append F D))
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
        exact hsame_trans (hsame_symm sameRows) sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr sourceRow))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow, rfl, rfl⟩
  }
  exact ⟨rfl, rfl, rfl, cert⟩

end BEDC.Derived.VerificationFailureRoadmapUp
