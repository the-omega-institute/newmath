import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionHistoryCarrier_hsame_branch_alignment {source : BHist → Prop}
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {h k : BHist} :
    OptionHistoryCarrier source h → OptionHistoryCarrier source k → hsame h k →
      (hsame h BHist.Empty ∧ hsame k BHist.Empty) ∨ (source h ∧ source k) := by
  intro carrierH carrierK sameHK
  cases carrierH with
  | inl emptyH =>
      cases carrierK with
      | inl emptyK =>
          exact Or.inl (And.intro emptyH emptyK)
      | inr sourceK =>
          exact False.elim
            (sourceExcludesEmpty k sourceK (hsame_trans (hsame_symm sameHK) emptyH))
  | inr sourceH =>
      cases carrierK with
      | inl emptyK =>
          exact False.elim (sourceExcludesEmpty h sourceH (hsame_trans sameHK emptyK))
      | inr sourceK =>
          exact Or.inr (And.intro sourceH sourceK)

end BEDC.Derived.OptionUp
