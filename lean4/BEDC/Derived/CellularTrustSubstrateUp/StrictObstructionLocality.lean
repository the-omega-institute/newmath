import BEDC.Derived.CellularTrustSubstrateUp.TasteGate

namespace BEDC.Derived.CellularTrustSubstrateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CellularTrustSubstrate_strict_obstruction_locality
    {R W K M A H C P N refusalRead blockedRead : BHist}
    (manifestAudit : Cont M A refusalRead)
    (refusalLocal : Cont refusalRead N blockedRead) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row M ∧
            ∃ packet : TasteGate.CellularTrustSubstrateUp,
              packet = TasteGate.CellularTrustSubstrateUp.mk R W K M A H C P N)
        (fun row : BHist =>
          hsame row M ∧ Cont M A refusalRead ∧ Cont refusalRead N blockedRead)
        (fun row : BHist => hsame row M ∧ hsame H H ∧ hsame P P ∧ hsame N N)
        hsame ∧
      Cont M A refusalRead ∧ Cont refusalRead N blockedRead ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row M ∧
            ∃ packet : TasteGate.CellularTrustSubstrateUp,
              packet = TasteGate.CellularTrustSubstrateUp.mk R W K M A H C P N)
        (fun row : BHist =>
          hsame row M ∧ Cont M A refusalRead ∧ Cont refusalRead N blockedRead)
        (fun row : BHist => hsame row M ∧ hsame H H ∧ hsame P P ∧ hsame N N)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro M
          ⟨hsame_refl M,
            Exists.intro (TasteGate.CellularTrustSubstrateUp.mk R W K M A H C P N) rfl⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, manifestAudit, refusalLocal⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, hsame_refl H, hsame_refl P, hsame_refl N⟩
  }
  exact ⟨cert, manifestAudit, refusalLocal, hsame_refl N⟩

end BEDC.Derived.CellularTrustSubstrateUp
