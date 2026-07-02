import BEDC.Derived.SubjectReductionRouteChoiceUp.ObligationSurface

namespace BEDC.Derived.SubjectReductionRouteChoiceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SubjectReductionRouteChoiceConfluenceNonescape
    {B V O H C P N bundleRead obstructionRead publicRead confluenceRead : BHist}
    (bundleRoute : Cont B V bundleRead)
    (obstructionRoute : Cont O H obstructionRead)
    (publicRoute : Cont bundleRead obstructionRead publicRead)
    (confluenceRoute : Cont publicRead C confluenceRead) :
    SemanticNameCert
        (fun row : BHist => hsame row confluenceRead)
        (fun row : BHist =>
          SubjectReductionRouteChoiceObligationRowSpec B V O H C P N row ∨
            hsame row bundleRead ∨ hsame row obstructionRead ∨ hsame row publicRead ∨
              hsame row confluenceRead)
        (fun row : BHist =>
          hsame row confluenceRead ∧ Cont B V bundleRead ∧ Cont O H obstructionRead ∧
            Cont bundleRead obstructionRead publicRead ∧ Cont publicRead C confluenceRead)
        hsame ∧
      Cont B V bundleRead ∧
        Cont O H obstructionRead ∧
          Cont bundleRead obstructionRead publicRead ∧ Cont publicRead C confluenceRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert NameCert
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row confluenceRead)
          (fun row : BHist =>
            SubjectReductionRouteChoiceObligationRowSpec B V O H C P N row ∨
              hsame row bundleRead ∨ hsame row obstructionRead ∨ hsame row publicRead ∨
                hsame row confluenceRead)
          (fun row : BHist =>
            hsame row confluenceRead ∧ Cont B V bundleRead ∧ Cont O H obstructionRead ∧
              Cont bundleRead obstructionRead publicRead ∧ Cont publicRead C confluenceRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro confluenceRead (hsame_refl confluenceRead)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source)))
    ledger_sound := by
      intro _row source
      exact ⟨source, bundleRoute, obstructionRoute, publicRoute, confluenceRoute⟩
  }
  exact ⟨cert, bundleRoute, obstructionRoute, publicRoute, confluenceRoute⟩

end BEDC.Derived.SubjectReductionRouteChoiceUp
