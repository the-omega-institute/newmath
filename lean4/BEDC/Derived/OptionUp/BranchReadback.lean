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

theorem OptionHistoryClassifier_exclusive_readback {source : BHist -> Prop}
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {h k : BHist} :
    OptionHistoryClassifier source h k ->
      (hsame h BHist.Empty ∧ hsame k BHist.Empty ∧
          (source h -> False) ∧ (source k -> False)) ∨
        (source h ∧ source k ∧ (hsame h BHist.Empty -> False) ∧
          (hsame k BHist.Empty -> False) ∧ hsame h k) := by
  intro classifier
  cases classifier with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          have readH := OptionHistoryCarrier_exclusive_readback sourceExcludesEmpty carrierH
          have readK := OptionHistoryCarrier_exclusive_readback sourceExcludesEmpty carrierK
          cases readH with
          | inl absentH =>
              cases readK with
              | inl absentK =>
                  exact Or.inl
                    (And.intro absentH.left
                      (And.intro absentK.left (And.intro absentH.right absentK.right)))
              | inr presentK =>
                  exact False.elim
                    (presentK.right (hsame_trans (hsame_symm sameHK) absentH.left))
          | inr presentH =>
              cases readK with
              | inl absentK =>
                  exact False.elim (presentH.right (hsame_trans sameHK absentK.left))
              | inr presentK =>
                  exact Or.inr
                    (And.intro presentH.left
                      (And.intro presentK.left
                        (And.intro presentH.right
                          (And.intro presentK.right sameHK))))

theorem OptionHistoryClassifier_source_left_exactness {source : BHist -> Prop}
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {h k : BHist} :
    source h -> (OptionHistoryClassifier source h k ↔ source k ∧ hsame h k) := by
  intro sourceH
  constructor
  · intro classifier
    cases classifier with
    | intro _carrierH rest =>
        cases rest with
        | intro carrierK sameHK =>
            constructor
            · cases carrierK with
              | inl sameKEmpty =>
                  exact False.elim (sourceExcludesEmpty h sourceH (hsame_trans sameHK sameKEmpty))
              | inr sourceK =>
                  exact sourceK
            · exact sameHK
  · intro sourceAndSame
    cases sourceAndSame with
    | intro sourceK sameHK =>
        exact And.intro (Or.inr sourceH) (And.intro (Or.inr sourceK) sameHK)

theorem OptionHistoryClassifier_source_right_exactness {source : BHist -> Prop}
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {h k : BHist} :
    source k -> (OptionHistoryClassifier source h k ↔ source h ∧ hsame h k) := by
  intro sourceK
  constructor
  · intro classifier
    cases classifier with
    | intro carrierH rest =>
        cases rest with
        | intro _carrierK sameHK =>
            constructor
            · cases carrierH with
              | inl sameHEmpty =>
                  exact False.elim
                    (sourceExcludesEmpty k sourceK (hsame_trans (hsame_symm sameHK) sameHEmpty))
              | inr sourceH =>
                  exact sourceH
            · exact sameHK
  · intro sourceAndSame
    cases sourceAndSame with
    | intro sourceH sameHK =>
        exact And.intro (Or.inr sourceH) (And.intro (Or.inr sourceK) sameHK)

end BEDC.Derived.OptionUp
