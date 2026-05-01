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

theorem TaggedOptionHistoryClassifier_carrier_mixed_tag_separation {S : BHist → Prop}
    {Rel : BHist → BHist → Prop} {h k a : BHist} :
    (hsame h BHist.Empty -> S a -> hsame k (BHist.e1 a) ->
      TaggedOptionHistoryClassifier S Rel h k -> False) ∧
      (S a -> hsame h (BHist.e1 a) -> hsame k BHist.Empty ->
        TaggedOptionHistoryClassifier S Rel h k -> False) := by
  constructor
  · intro sameHEmpty _sourceA sameKPresent classifier
    cases classifier with
    | inl absentPair =>
        exact not_hsame_emp_e1 (hsame_trans (hsame_symm absentPair.right) sameKPresent)
    | inr presentPair =>
        cases presentPair with
        | intro b restB =>
            cases restB with
            | intro c data =>
                cases data with
                | intro _sourceB rest =>
                    cases rest with
                    | intro _sourceC rest =>
                        cases rest with
                        | intro sameHPresent _rest =>
                            exact not_hsame_emp_e1
                              (hsame_trans (hsame_symm sameHEmpty) sameHPresent)
  · intro _sourceA sameHPresent sameKEmpty classifier
    cases classifier with
    | inl absentPair =>
        exact not_hsame_emp_e1 (hsame_trans (hsame_symm absentPair.left) sameHPresent)
    | inr presentPair =>
        cases presentPair with
        | intro b restB =>
            cases restB with
            | intro c data =>
                cases data with
                | intro _sourceB rest =>
                    cases rest with
                    | intro _sourceC rest =>
                        cases rest with
                        | intro _sameHPresent rest =>
                            cases rest with
                            | intro sameKPresent _rel =>
                                exact not_hsame_e1_empty
                                  (hsame_trans (hsame_symm sameKPresent) sameKEmpty)

theorem TaggedOptionHistoryClassifier_endpoint_carriers {S : BHist → Prop}
    {Rel : BHist → BHist → Prop} {h k : BHist} :
    TaggedOptionHistoryClassifier S Rel h k →
      TaggedOptionHistoryCarrier S h ∧ TaggedOptionHistoryCarrier S k := by
  intro classifier
  cases classifier with
  | inl absent =>
      constructor
      · exact Or.inl absent.left
      · exact Or.inl absent.right
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
                      | intro sameH rest =>
                          cases rest with
                          | intro sameK _rel =>
                              constructor
                              · exact Or.inr (Exists.intro a (And.intro sourceA sameH))
                              · exact Or.inr (Exists.intro b (And.intro sourceB sameK))

theorem TaggedOptionHistoryClassifier_exclusive_branch_readback {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      (hsame h BHist.Empty ∧ hsame k BHist.Empty ∧
          ((∃ a : BHist, S a ∧ hsame h (BHist.e1 a)) -> False) ∧
          ((∃ b : BHist, S b ∧ hsame k (BHist.e1 b)) -> False)) ∨
        (∃ a b : BHist,
          S a ∧ S b ∧ hsame h (BHist.e1 a) ∧ hsame k (BHist.e1 b) ∧ Rel a b ∧
            (hsame h BHist.Empty -> False) ∧ (hsame k BHist.Empty -> False)) := by
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
                                                      (hsame_symm sameHPresent) sameHEmpty))
                                                (by
                                                  intro sameKEmpty
                                                  exact not_hsame_e1_empty
                                                    (hsame_trans
                                                      (hsame_symm sameKPresent) sameKEmpty))))))))))

end BEDC.Derived.OptionUp
