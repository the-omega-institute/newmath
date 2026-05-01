import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_exclusive_branch_readback {S : BHist → Prop}
    {Rel : BHist → BHist → Prop} {h k : BHist} :
    TaggedOptionHistoryClassifier S Rel h k →
      (hsame h BHist.Empty ∧ hsame k BHist.Empty ∧
        ((∃ a : BHist, S a ∧ hsame h (BHist.e1 a)) → False) ∧
        ((∃ b : BHist, S b ∧ hsame k (BHist.e1 b)) → False)) ∨
        (∃ a : BHist, ∃ b : BHist,
          S a ∧ S b ∧ hsame h (BHist.e1 a) ∧ hsame k (BHist.e1 b) ∧ Rel a b ∧
            (hsame h BHist.Empty → False) ∧ (hsame k BHist.Empty → False)) := by
  intro classifier
  cases classifier with
  | inl absent =>
      exact Or.inl
        (And.intro absent.left
          (And.intro absent.right
            (And.intro
              (by
                intro presentH
                cases presentH with
                | intro a data =>
                    cases data with
                    | intro _sourceA sameHPresent =>
                        exact not_hsame_emp_e1
                          (hsame_trans (hsame_symm absent.left) sameHPresent))
              (by
                intro presentK
                cases presentK with
                | intro b data =>
                    cases data with
                    | intro _sourceB sameKPresent =>
                        exact not_hsame_emp_e1
                          (hsame_trans (hsame_symm absent.right) sameKPresent)))))
  | inr present =>
      cases present with
      | intro a restA =>
          cases restA with
          | intro b data =>
              cases data with
              | intro sourceA rest =>
                  cases rest with
                  | intro sourceB rest =>
                      cases rest with
                      | intro sameHPresent rest =>
                          cases rest with
                          | intro sameKPresent relAB =>
                              exact Or.inr
                                (Exists.intro a
                                  (Exists.intro b
                                    (And.intro sourceA
                                      (And.intro sourceB
                                        (And.intro sameHPresent
                                          (And.intro sameKPresent
                                            (And.intro relAB
                                              (And.intro
                                                (by
                                                  intro sameHEmpty
                                                  exact not_hsame_e1_empty
                                                    (hsame_trans
                                                      (hsame_symm sameHPresent)
                                                      sameHEmpty))
                                                (by
                                                  intro sameKEmpty
                                                  exact not_hsame_e1_empty
                                                    (hsame_trans
                                                      (hsame_symm sameKPresent)
                                                      sameKEmpty))))))))))

end BEDC.Derived.OptionUp
