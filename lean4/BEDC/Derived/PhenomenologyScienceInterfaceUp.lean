import BEDC.Derived.PhenomenologyScienceInterfaceUp.TasteGate

namespace BEDC.Derived.PhenomenologyScienceInterfaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem PhenomenologyScienceInterface_tastegate_obligation_scope
    {R U O L S J B G H C P N observationReplay scienceReplay : BHist}
    (observationRoute : Cont R U observationReplay)
    (scienceRoute : Cont S J scienceReplay) :
    SemanticNameCert
      (fun row : BHist => hsame row observationReplay ∨ hsame row scienceReplay)
      (fun row : BHist =>
        PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N row ∨
          hsame row observationReplay ∨ hsame row scienceReplay)
      (fun row : BHist =>
        (hsame row observationReplay ∧ Cont R U observationReplay) ∨
          (hsame row scienceReplay ∧ Cont S J scienceReplay))
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro observationReplay (Or.inl (hsame_refl observationReplay))
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
        have sameOtherRow : hsame _other _row := hsame_symm sameRows
        cases source with
        | inl sameObservation =>
            exact Or.inl (hsame_trans sameOtherRow sameObservation)
        | inr sameScience =>
            exact Or.inr (hsame_trans sameOtherRow sameScience)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameObservation =>
          exact Or.inr (Or.inl sameObservation)
      | inr sameScience =>
          exact Or.inr (Or.inr sameScience)
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameObservation =>
          exact Or.inl ⟨sameObservation, observationRoute⟩
      | inr sameScience =>
          exact Or.inr ⟨sameScience, scienceRoute⟩
  }

end BEDC.Derived.PhenomenologyScienceInterfaceUp
