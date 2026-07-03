import BEDC.Derived.FinitePrefixStreamUp.RealCompletionBudgetRoute

namespace BEDC.Derived.FinitePrefixStreamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem FinitePrefixStreamCompletionSectionPullback
    {k W D R H C P N sectionRow : BHist} :
    Cont k W D →
      Cont D R sectionRow →
        hsame H H →
          Nonempty (NameCert (fun row : BHist => hsame row sectionRow) hsame) →
            SemanticNameCert
                (fun row : BHist => hsame row sectionRow)
                (fun row : BHist =>
                  hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                      hsame row sectionRow)
                (fun row : BHist => hsame row sectionRow ∧ Cont D R sectionRow)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert SemanticNameCert
  intro _prefixRoute sectionRoute _visibleSelf sectionCert
  cases sectionCert with
  | intro sectionCore =>
      exact {
        core := {
          carrier_inhabited := sectionCore.carrier_inhabited
          equiv_refl := by
            intro row source
            exact hsame_trans (sectionCore.equiv_refl source) (hsame_refl row)
          equiv_symm := by
            intro _row _other sameRows
            exact sectionCore.equiv_symm sameRows
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact sectionCore.equiv_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro _row _other sameRows source
            exact sectionCore.carrier_respects_equiv sameRows source
        }
        pattern_sound := by
          intro _row source
          exact
            Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source)))))))
        ledger_sound := by
          intro _row source
          exact ⟨source, sectionRoute⟩
      }

end BEDC.Derived.FinitePrefixStreamUp
