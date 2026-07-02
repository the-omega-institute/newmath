import BEDC.Derived.PhenomenologyScienceInterfaceUp.ObligationCarrier

namespace BEDC.Derived.PhenomenologyScienceInterfaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem PhenomenologyScienceInterfaceObligationClassifier
    {R U O L S J B G H C P N observationRead scienceRead bridgeRead : BHist}
    (observationRoute : Cont R U observationRead)
    (scienceRoute : Cont S J scienceRead)
    (bridgeRoute : Cont scienceRead B bridgeRead) :
    SemanticNameCert
        (fun row : BHist => hsame row bridgeRead)
        (fun row : BHist =>
          PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N row ∨
            hsame row observationRead ∨ hsame row scienceRead ∨ hsame row bridgeRead)
        (fun row : BHist =>
          hsame row bridgeRead ∧ Cont R U observationRead ∧ Cont S J scienceRead ∧
            Cont scienceRead B bridgeRead)
        hsame ∧
      PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N R ∧
        PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N S ∧
          Cont R U observationRead ∧ Cont S J scienceRead ∧
            Cont scienceRead B bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead)
          (fun row : BHist =>
            PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N row ∨
              hsame row observationRead ∨ hsame row scienceRead ∨ hsame row bridgeRead)
          (fun row : BHist =>
            hsame row bridgeRead ∧ Cont R U observationRead ∧ Cont S J scienceRead ∧
              Cont scienceRead B bridgeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead (hsame_refl bridgeRead)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨source, observationRoute, scienceRoute, bridgeRoute⟩
  }
  exact
    ⟨cert, Or.inl (hsame_refl R),
      Or.inr
        (Or.inr
          (Or.inr
            (Or.inr (Or.inl (hsame_refl S))))),
      observationRoute, scienceRoute, bridgeRoute⟩

end BEDC.Derived.PhenomenologyScienceInterfaceUp
