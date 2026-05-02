import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryCarrier_exclusive_branch_iff {S : BHist → Prop} {h : BHist} :
    TaggedOptionHistoryCarrier S h ↔
      (hsame h BHist.Empty ∧ ((∃ a : BHist, S a ∧ hsame h (BHist.e1 a)) → False)) ∨
        (∃ a : BHist, S a ∧ hsame h (BHist.e1 a) ∧
          (hsame h BHist.Empty → False)) := by
  constructor
  · intro carrier
    exact TaggedOptionHistoryCarrier_exclusive_branch_partition carrier
  · intro branches
    cases branches with
    | inl absent =>
        exact Or.inl absent.left
    | inr present =>
        cases present with
        | intro a data =>
            exact Or.inr (Exists.intro a (And.intro data.left data.right.left))

end BEDC.Derived.OptionUp
