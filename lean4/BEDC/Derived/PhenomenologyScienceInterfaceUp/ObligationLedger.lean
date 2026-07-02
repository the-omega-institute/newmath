import BEDC.Derived.PhenomenologyScienceInterfaceUp.ObligationClassifier

namespace BEDC.Derived.PhenomenologyScienceInterfaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem PhenomenologyScienceInterface_obligation_ledger
    {R U O L S J B G H C P N ledgerRead : BHist}
    (ledgerRoute : Cont H C ledgerRead) :
    SemanticNameCert
        (fun row : BHist =>
          PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N row)
        (fun row : BHist =>
          PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N row ∨
            hsame row ledgerRead)
        (fun row : BHist =>
          PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N row ∧
            Cont H C ledgerRead)
        hsame ∧
      Cont H C ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro R (Or.inl (hsame_refl R))
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
          cases sameRows
          exact source
      }
      pattern_sound := by
        intro _row source
        exact Or.inl source
      ledger_sound := by
        intro _row source
        exact And.intro source ledgerRoute
    }
  · exact ledgerRoute

end BEDC.Derived.PhenomenologyScienceInterfaceUp
