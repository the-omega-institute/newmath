import BEDC.Derived.PhilosophyCannotClaimRegistryUp.StatusExactness

namespace BEDC.Derived.PhilosophyCannotClaimRegistryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem PhilosophyCannotClaimRegistryGateInduction
    {C S E U B H K P N statusRead reasonRead upgradeRead blockRead replayRead : BHist} :
    Cont C S statusRead →
      Cont statusRead E reasonRead →
        Cont reasonRead U upgradeRead →
          Cont upgradeRead B blockRead →
            Cont blockRead K replayRead →
              UnaryHistory C →
                UnaryHistory S →
                  UnaryHistory E →
                    UnaryHistory U →
                      UnaryHistory B →
                        UnaryHistory K →
                          SemanticNameCert
                              (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row C ∨ hsame row S ∨ hsame row E ∨
                                  hsame row U ∨ hsame row B ∨ hsame row replayRead)
                              (fun row : BHist =>
                                Cont C S statusRead ∧ Cont statusRead E reasonRead ∧
                                  Cont reasonRead U upgradeRead ∧
                                    Cont upgradeRead B blockRead ∧
                                      Cont blockRead K replayRead ∧
                                        hsame row replayRead)
                              hsame ∧
                            UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro claimStatus statusReason reasonUpgrade upgradeBlock blockReplay claimUnary
    statusUnary exclusionUnary upgradeUnary blockUnary replayCarrierUnary
  have statusReadUnary : UnaryHistory statusRead :=
    unary_cont_closed claimUnary statusUnary claimStatus
  have reasonReadUnary : UnaryHistory reasonRead :=
    unary_cont_closed statusReadUnary exclusionUnary statusReason
  have upgradeReadUnary : UnaryHistory upgradeRead :=
    unary_cont_closed reasonReadUnary upgradeUnary reasonUpgrade
  have blockReadUnary : UnaryHistory blockRead :=
    unary_cont_closed upgradeReadUnary blockUnary upgradeBlock
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed blockReadUnary replayCarrierUnary blockReplay
  have sourceReplay :
      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row) replayRead := by
    exact ⟨hsame_refl replayRead, replayReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row S ∨ hsame row E ∨
              hsame row U ∨ hsame row B ∨ hsame row replayRead)
          (fun row : BHist =>
            Cont C S statusRead ∧ Cont statusRead E reasonRead ∧
              Cont reasonRead U upgradeRead ∧ Cont upgradeRead B blockRead ∧
                Cont blockRead K replayRead ∧ hsame row replayRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead sourceReplay
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨claimStatus, statusReason, reasonUpgrade, upgradeBlock, blockReplay,
          source.left⟩
  }
  exact ⟨cert, replayReadUnary⟩

end BEDC.Derived.PhilosophyCannotClaimRegistryUp
