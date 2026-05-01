import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_branch_exactness {S : BHist → Prop}
    {Rel : BHist → BHist → Prop} {h k : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ↔
      (hsame h BHist.Empty ∧ hsame k BHist.Empty) ∨
        (∃ a b : BHist,
          S a ∧ S b ∧ hsame h (BHist.e1 a) ∧ hsame k (BHist.e1 b) ∧ Rel a b) := by
  constructor
  · intro classified
    cases classified with
    | inl absent =>
        exact Or.inl absent
    | inr present =>
        cases present with
        | intro a rest =>
            cases rest with
            | intro b data =>
                exact Or.inr (Exists.intro a (Exists.intro b data))
  · intro branch
    cases branch with
    | inl absent =>
        exact Or.inl absent
    | inr present =>
        cases present with
        | intro a rest =>
            cases rest with
            | intro b data =>
                exact Or.inr (Exists.intro a (Exists.intro b data))

theorem TaggedOptionHistory_present_payload_determinism {h a b : BHist} :
    hsame h (BHist.e1 a) → hsame h (BHist.e1 b) → hsame a b := by
  intro sameA sameB
  exact hsame_e1_iff.mp (hsame_trans (hsame_symm sameA) sameB)

theorem TaggedOptionHistoryClassifier_right_absent_exactness {S : BHist → Prop}
    {Rel : BHist → BHist → Prop} {h : BHist} :
    TaggedOptionHistoryClassifier S Rel h BHist.Empty ↔ hsame h BHist.Empty := by
  constructor
  · intro classified
    cases classified with
    | inl absent =>
        exact absent.left
    | inr present =>
        cases present with
        | intro _ rest =>
            cases rest with
            | intro b data =>
                cases data with
                | intro _ rest =>
                    cases rest with
                    | intro _ rest =>
                        cases rest with
                        | intro _ rest =>
                            cases rest with
                            | intro sameRightPresent _ =>
                                exact False.elim (not_hsame_emp_e1 sameRightPresent)
  · intro sameEmpty
    exact Or.inl (And.intro sameEmpty (hsame_refl BHist.Empty))

end BEDC.Derived.OptionUp
