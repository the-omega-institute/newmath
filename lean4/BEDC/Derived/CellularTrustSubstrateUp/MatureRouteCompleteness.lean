import BEDC.Derived.CellularTrustSubstrateUp.TasteGate

namespace BEDC.Derived.CellularTrustSubstrateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CellularTrustSubstrate_mature_route_completeness
    {R W K M A H C P N publicRead bridgeRead matureRead : BHist}
    (ruleRoute : Cont R W K)
    (manifestRoute : Cont K M A)
    (publicRoute : Cont A N publicRead)
    (bridgeRoute : Cont A N bridgeRead)
    (matureRoute : Cont publicRead bridgeRead matureRead) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row R ∧
            ∃ packet : TasteGate.CellularTrustSubstrateUp,
              packet = TasteGate.CellularTrustSubstrateUp.mk R W K M A H C P N)
        (fun row : BHist =>
          hsame row R ∧ Cont R W K ∧ Cont K M A ∧ Cont A N publicRead ∧
            Cont A N bridgeRead ∧ Cont publicRead bridgeRead matureRead)
        (fun row : BHist => hsame row R ∧ hsame H H ∧ hsame P P ∧ hsame N N)
        hsame ∧
      Cont R W K ∧ Cont K M A ∧ Cont A N publicRead ∧ Cont A N bridgeRead ∧
        Cont publicRead bridgeRead matureRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row R ∧
            ∃ packet : TasteGate.CellularTrustSubstrateUp,
              packet = TasteGate.CellularTrustSubstrateUp.mk R W K M A H C P N)
        (fun row : BHist =>
          hsame row R ∧ Cont R W K ∧ Cont K M A ∧ Cont A N publicRead ∧
            Cont A N bridgeRead ∧ Cont publicRead bridgeRead matureRead)
        (fun row : BHist => hsame row R ∧ hsame H H ∧ hsame P P ∧ hsame N N)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro R
          ⟨hsame_refl R,
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
      exact ⟨source.left, ruleRoute, manifestRoute, publicRoute, bridgeRoute, matureRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, hsame_refl H, hsame_refl P, hsame_refl N⟩
  }
  exact ⟨cert, ruleRoute, manifestRoute, publicRoute, bridgeRoute, matureRoute⟩

end BEDC.Derived.CellularTrustSubstrateUp
