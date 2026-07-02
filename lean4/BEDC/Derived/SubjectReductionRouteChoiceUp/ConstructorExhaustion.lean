import BEDC.Derived.SubjectReductionRouteChoiceUp.ObligationSurface

namespace BEDC.Derived.SubjectReductionRouteChoiceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SubjectReductionRouteChoiceConstructorExhaustion
    {B V O H C P N bundleRead obstructionRead : BHist}
    (bundleRoute : Cont B V bundleRead)
    (obstructionRoute : Cont O H obstructionRead) :
    SubjectReductionRouteChoiceObligationRowSpec B V O H C P N B ∧
      SubjectReductionRouteChoiceObligationRowSpec B V O H C P N V ∧
        SubjectReductionRouteChoiceObligationRowSpec B V O H C P N O ∧
          Cont B V bundleRead ∧
            Cont O H obstructionRead ∧
              SemanticNameCert
                (fun row : BHist => hsame row bundleRead ∨ hsame row obstructionRead)
                (fun row : BHist =>
                  SubjectReductionRouteChoiceObligationRowSpec B V O H C P N row ∨
                    hsame row bundleRead ∨ hsame row obstructionRead)
                (fun row : BHist =>
                  (hsame row bundleRead ∧ Cont B V bundleRead) ∨
                    (hsame row obstructionRead ∧ Cont O H obstructionRead))
                hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert NameCert
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row bundleRead ∨ hsame row obstructionRead)
        (fun row : BHist =>
          SubjectReductionRouteChoiceObligationRowSpec B V O H C P N row ∨
            hsame row bundleRead ∨ hsame row obstructionRead)
        (fun row : BHist =>
          (hsame row bundleRead ∧ Cont B V bundleRead) ∨
            (hsame row obstructionRead ∧ Cont O H obstructionRead))
        hsame := {
    core := {
      carrier_inhabited := Exists.intro bundleRead (Or.inl (hsame_refl bundleRead))
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
        cases source with
        | inl sameBundle =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameBundle)
        | inr sameObstruction =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameObstruction)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameBundle =>
          exact Or.inr (Or.inl sameBundle)
      | inr sameObstruction =>
          exact Or.inr (Or.inr sameObstruction)
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameBundle =>
          exact Or.inl ⟨sameBundle, bundleRoute⟩
      | inr sameObstruction =>
          exact Or.inr ⟨sameObstruction, obstructionRoute⟩
  }
  exact
    ⟨Or.inl (hsame_refl B),
      Or.inr (Or.inl (hsame_refl V)),
      Or.inr (Or.inr (Or.inl (hsame_refl O))),
      bundleRoute,
      obstructionRoute,
      cert⟩

end BEDC.Derived.SubjectReductionRouteChoiceUp
