import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryCarrier_present_hsame_readback {S : BHist → Prop} {h p : BHist} :
    TaggedOptionHistoryCarrier S h →
      hsame h (BHist.e1 p) → ∃ a : BHist, S a ∧ hsame p a := by
  intro carrier samePresent
  cases carrier with
  | inl emptyCase =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm emptyCase) samePresent))
  | inr presentCase =>
      cases presentCase with
      | intro a data =>
          cases data with
          | intro sourceA sameEndpoint =>
              exact Exists.intro a
                (And.intro sourceA
                  (hsame_e1_iff.mp (hsame_trans (hsame_symm samePresent) sameEndpoint)))

end BEDC.Derived.OptionUp
