import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_right_present_payload_fanout {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k r a : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      TaggedOptionHistoryClassifier S Rel r k ->
        hsame k (BHist.e1 a) ->
          (exists b a' : BHist,
            S b /\ S a' /\ hsame a a' /\ Rel b a' /\ hsame h (BHist.e1 b)) /\
            (exists c a'' : BHist,
              S c /\ S a'' /\ hsame a a'' /\ Rel c a'' /\ hsame r (BHist.e1 c)) := by
  intro left right sameK
  constructor
  · cases left with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.right) sameK))
    | inr present =>
        cases present with
        | intro b restB =>
            cases restB with
            | intro a' data =>
                cases data with
                | intro sourceB rest =>
                    cases rest with
                    | intro sourceA rest =>
                        cases rest with
                        | intro sameH rest =>
                            cases rest with
                            | intro sameKPresent rel =>
                                have samePayload : hsame a a' :=
                                  hsame_e1_iff.mp (hsame_trans (hsame_symm sameK) sameKPresent)
                                exact Exists.intro b
                                  (Exists.intro a'
                                    (And.intro sourceB
                                      (And.intro sourceA
                                        (And.intro samePayload (And.intro rel sameH)))))
  · cases right with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.right) sameK))
    | inr present =>
        cases present with
        | intro c restC =>
            cases restC with
            | intro a'' data =>
                cases data with
                | intro sourceC rest =>
                    cases rest with
                    | intro sourceA rest =>
                        cases rest with
                        | intro sameR rest =>
                            cases rest with
                            | intro sameKPresent rel =>
                                have samePayload : hsame a a'' :=
                                  hsame_e1_iff.mp (hsame_trans (hsame_symm sameK) sameKPresent)
                                exact Exists.intro c
                                  (Exists.intro a''
                                    (And.intro sourceC
                                      (And.intro sourceA
                                        (And.intro samePayload (And.intro rel sameR)))))

end BEDC.Derived.OptionUp
