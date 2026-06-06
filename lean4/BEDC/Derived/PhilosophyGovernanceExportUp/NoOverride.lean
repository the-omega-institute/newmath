import BEDC.Derived.PhilosophyGovernanceExportUp.TasteGate

namespace BEDC.Derived.PhilosophyGovernanceExportUp

open BEDC.FKernel.Hist

theorem PhilosophyGovernanceExportNoOverride (x : PhilosophyGovernanceExportUp) :
    ∃ P R L S C X T O H K N : BHist,
      x = PhilosophyGovernanceExportUp.mk P R L S C X T O H K N ∧
        philosophyGovernanceExportFields x = [P, R, L, S, C, X, T, O, H, K, N] := by
  -- BEDC touchpoint anchor: BHist
  cases x with
  | mk P R L S C X T O H K N =>
      exact ⟨P, R, L, S, C, X, T, O, H, K, N, rfl, rfl⟩

end BEDC.Derived.PhilosophyGovernanceExportUp
