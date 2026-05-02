import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_left_present_payload_fanout {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k r a : BHist} :
    TaggedOptionHistoryClassifier S Rel h k -> TaggedOptionHistoryClassifier S Rel h r ->
      hsame h (BHist.e1 a) ->
        (exists b a' : BHist, S b /\ S a' /\ hsame a a' /\ Rel a' b /\
          hsame k (BHist.e1 b)) /\
          (exists c a'' : BHist, S c /\ S a'' /\ hsame a a'' /\ Rel a'' c /\
            hsame r (BHist.e1 c)) := by
  intro left right sameHPresent
  constructor
  · cases left with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameHPresent))
    | inr present =>
        cases present with
        | intro source restSource =>
            cases restSource with
            | intro target data =>
                have samePayload : hsame a source :=
                  hsame_e1_iff.mp
                    (hsame_trans (hsame_symm sameHPresent) data.right.right.left)
                exact Exists.intro target
                  (Exists.intro source
                    (And.intro data.right.left
                      (And.intro data.left
                        (And.intro samePayload
                          (And.intro data.right.right.right.right
                            data.right.right.right.left)))))
  · cases right with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameHPresent))
    | inr present =>
        cases present with
        | intro source restSource =>
            cases restSource with
            | intro target data =>
                have samePayload : hsame a source :=
                  hsame_e1_iff.mp
                    (hsame_trans (hsame_symm sameHPresent) data.right.right.left)
                exact Exists.intro target
                  (Exists.intro source
                    (And.intro data.right.left
                      (And.intro data.left
                        (And.intro samePayload
                          (And.intro data.right.right.right.right
                            data.right.right.right.left)))))

end BEDC.Derived.OptionUp
