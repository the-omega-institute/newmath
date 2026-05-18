import BEDC.Derived.CellularTrustSubstrateUp.TasteGate

namespace BEDC.Derived.CellularTrustSubstrateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CellularTrustSubstrate_sibling_scope_binding
    {R W K M A H C P N automatonTrace boundedTrace substrateLocal localityRead siblingRead :
      BHist}
    (ruleRoute : Cont R W automatonTrace)
    (boundedRoute : Cont automatonTrace K boundedTrace)
    (manifestRoute : Cont M A substrateLocal)
    (localityRoute : Cont substrateLocal N localityRead)
    (siblingRoute : Cont boundedTrace localityRead siblingRead) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row R ∧
            ∃ packet : TasteGate.CellularTrustSubstrateUp,
              packet = TasteGate.CellularTrustSubstrateUp.mk R W K M A H C P N)
        (fun row : BHist =>
          hsame row R ∧ Cont R W automatonTrace ∧
            Cont automatonTrace K boundedTrace ∧ Cont M A substrateLocal ∧
              Cont substrateLocal N localityRead)
        (fun row : BHist =>
          hsame row R ∧ Cont boundedTrace localityRead siblingRead ∧ hsame H H ∧
            hsame P P ∧ hsame N N)
        hsame ∧
      Cont R W automatonTrace ∧ Cont automatonTrace K boundedTrace ∧
        Cont M A substrateLocal ∧ Cont substrateLocal N localityRead ∧
          Cont boundedTrace localityRead siblingRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row R ∧
            ∃ packet : TasteGate.CellularTrustSubstrateUp,
              packet = TasteGate.CellularTrustSubstrateUp.mk R W K M A H C P N)
        (fun row : BHist =>
          hsame row R ∧ Cont R W automatonTrace ∧
            Cont automatonTrace K boundedTrace ∧ Cont M A substrateLocal ∧
              Cont substrateLocal N localityRead)
        (fun row : BHist =>
          hsame row R ∧ Cont boundedTrace localityRead siblingRead ∧ hsame H H ∧
            hsame P P ∧ hsame N N)
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
      exact ⟨source.left, ruleRoute, boundedRoute, manifestRoute, localityRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, siblingRoute, hsame_refl H, hsame_refl P, hsame_refl N⟩
  }
  exact ⟨cert, ruleRoute, boundedRoute, manifestRoute, localityRoute, siblingRoute⟩

end BEDC.Derived.CellularTrustSubstrateUp
