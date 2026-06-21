import BEDC.Derived.PhilosophyCannotClaimRegistryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.PhilosophyCannotClaimRegistryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem PhilosophyCannotClaimRegistryUpgradeBoundaryExhaustion
    {_C S _E U B _H K _P _N _statusRead blockRead upgradeRead replayRead : BHist} :
    Cont S U upgradeRead →
      Cont S B blockRead →
        Cont upgradeRead K replayRead →
          UnaryHistory S →
            UnaryHistory U →
              UnaryHistory B →
                UnaryHistory K →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row upgradeRead ∨ hsame row blockRead ∨
                            hsame row replayRead) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row U ∨ hsame row B ∨ hsame row K ∨
                          hsame row upgradeRead ∨ hsame row blockRead ∨
                            hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S U upgradeRead ∧
                          Cont S B blockRead ∧ Cont upgradeRead K replayRead)
                      hsame ∧
                    UnaryHistory upgradeRead ∧ UnaryHistory blockRead ∧
                      UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro statusUpgrade statusBlock upgradeReplay statusUnary upgradeUnary blockUnary
    replayUnary
  have upgradeReadUnary : UnaryHistory upgradeRead :=
    unary_cont_closed statusUnary upgradeUnary statusUpgrade
  have blockReadUnary : UnaryHistory blockRead :=
    unary_cont_closed statusUnary blockUnary statusBlock
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed upgradeReadUnary replayUnary upgradeReplay
  have replaySource :
      (fun row : BHist =>
        (hsame row upgradeRead ∨ hsame row blockRead ∨ hsame row replayRead) ∧
          UnaryHistory row) replayRead := by
    exact ⟨Or.inr (Or.inr (hsame_refl replayRead)), replayReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row upgradeRead ∨ hsame row blockRead ∨ hsame row replayRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row B ∨ hsame row K ∨
              hsame row upgradeRead ∨ hsame row blockRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S U upgradeRead ∧ Cont S B blockRead ∧
              Cont upgradeRead K replayRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead replaySource
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
        intro _row _other sameRows source
        constructor
        · cases source.left with
          | inl sameUpgrade =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameUpgrade)
          | inr rest =>
              cases rest with
              | inl sameBlock =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameBlock))
              | inr sameReplay =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameReplay))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameUpgrade =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameUpgrade))))
      | inr rest =>
          cases rest with
          | inl sameBlock =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameBlock)))))
          | inr sameReplay =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inr (Or.inr sameReplay)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, statusUpgrade, statusBlock, upgradeReplay⟩
  }
  exact ⟨cert, upgradeReadUnary, blockReadUnary, replayReadUnary⟩

end BEDC.Derived.PhilosophyCannotClaimRegistryUp
