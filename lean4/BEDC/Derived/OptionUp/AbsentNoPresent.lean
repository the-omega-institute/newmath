import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryCarrier_absent_no_present_iff {S : BHist → Prop} {h : BHist} :
    TaggedOptionHistoryCarrier S h →
      (hsame h BHist.Empty ↔ ((∃ a : BHist, S a ∧ hsame h (BHist.e1 a)) → False)) := by
  intro carrier
  constructor
  · intro sameEmpty present
    cases present with
    | intro a data =>
        cases data with
        | intro _ samePresent =>
            exact not_hsame_emp_e1 (hsame_trans (hsame_symm sameEmpty) samePresent)
  · intro noPresent
    cases carrier with
    | inl emptyCase =>
        exact emptyCase
    | inr presentCase =>
        exact False.elim (noPresent presentCase)

end BEDC.Derived.OptionUp
