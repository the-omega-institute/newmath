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

end BEDC.Derived.OptionUp
