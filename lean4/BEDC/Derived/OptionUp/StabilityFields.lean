import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionHistoryClassifier_stability_fields {S : BHist → Prop}
    {Rel : BHist → BHist → Prop} (cert : NameCert S Rel) :
    (∀ {h : BHist}, TaggedOptionHistoryCarrier S h →
      TaggedOptionHistoryClassifier S Rel h h) ∧
      (∀ {h k : BHist}, TaggedOptionHistoryClassifier S Rel h k →
        TaggedOptionHistoryClassifier S Rel k h) ∧
      (∀ {h k r : BHist}, TaggedOptionHistoryClassifier S Rel h k →
        TaggedOptionHistoryClassifier S Rel k r →
          TaggedOptionHistoryClassifier S Rel h r) ∧
      (∀ {h k : BHist}, TaggedOptionHistoryCarrier S h →
        TaggedOptionHistoryClassifier S Rel h k → TaggedOptionHistoryCarrier S k) ∧
      (∀ {h k h' k' : BHist}, TaggedOptionHistoryClassifier S Rel h k →
        hsame h h' → hsame k k' → TaggedOptionHistoryClassifier S Rel h' k') := by
  constructor
  · intro h carrier
    cases carrier with
    | inl emptyCase =>
        exact Or.inl (And.intro emptyCase emptyCase)
    | inr presentCase =>
        cases presentCase with
        | intro a data =>
            cases data with
            | intro sourceA samePresent =>
                exact Or.inr
                  (Exists.intro a
                    (Exists.intro a
                      (And.intro sourceA
                        (And.intro sourceA
                          (And.intro samePresent
                            (And.intro samePresent
                              (NameCert.equiv_refl cert sourceA)))))))
  · constructor
    · intro h k classified
      cases classified with
      | inl absent =>
          exact Or.inl (And.intro absent.right absent.left)
      | inr present =>
          cases present with
          | intro a rest =>
              cases rest with
              | intro b data =>
                  cases data with
                  | intro sourceA rest =>
                      cases rest with
                      | intro sourceB rest =>
                          cases rest with
                          | intro sameH rest =>
                              cases rest with
                              | intro sameK relAB =>
                                  exact Or.inr
                                    (Exists.intro b
                                      (Exists.intro a
                                        (And.intro sourceB
                                          (And.intro sourceA
                                            (And.intro sameK
                                              (And.intro sameH
                                                (NameCert.equiv_symm cert relAB)))))))
    · constructor
      · intro h k r classifiedHK classifiedKR
        exact TaggedOptionHistoryClassifier_trans
          (S := S) (Rel := Rel)
          (fun {a b c} relAB relBC => NameCert.equiv_trans cert relAB relBC)
          classifiedHK classifiedKR
      · constructor
        · intro h k _carrier classified
          cases classified with
          | inl absent =>
              exact Or.inl absent.right
          | inr present =>
              cases present with
              | intro _ rest =>
                  cases rest with
                  | intro b data =>
                      cases data with
                      | intro _ rest =>
                          cases rest with
                          | intro sourceB rest =>
                              cases rest with
                              | intro _ rest =>
                                  cases rest with
                                  | intro sameK _ =>
                                      exact Or.inr (Exists.intro b (And.intro sourceB sameK))
        · intro h k h' k' classified sameH sameK
          cases classified with
          | inl absent =>
              exact Or.inl
                (And.intro (hsame_trans (hsame_symm sameH) absent.left)
                  (hsame_trans (hsame_symm sameK) absent.right))
          | inr present =>
              cases present with
              | intro a rest =>
                  cases rest with
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
                                                (And.intro
                                                  (hsame_trans (hsame_symm sameH)
                                                    sameHPresent)
                                                  (And.intro
                                                    (hsame_trans (hsame_symm sameK)
                                                      sameKPresent)
                                                    relAB))))))

end BEDC.Derived.OptionUp
