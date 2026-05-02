import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_visible_payload_witnesses {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k a b : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      hsame h (BHist.e1 a) ->
        hsame k (BHist.e1 b) ->
          exists a' : BHist, exists b' : BHist,
            S a' /\ S b' /\ hsame a a' /\ hsame b b' /\ Rel a' b' := by
  intro classifier sameLeft sameRight
  cases classifier with
  | inl absent =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameLeft))
  | inr present =>
      cases present with
      | intro a' present =>
          cases present with
          | intro b' data =>
              have sameAA' : hsame a a' :=
                hsame_e1_iff.mp
                  (hsame_trans (hsame_symm sameLeft) data.right.right.left)
              have sameBB' : hsame b b' :=
                hsame_e1_iff.mp
                  (hsame_trans (hsame_symm sameRight) data.right.right.right.left)
              exact Exists.intro a'
                (Exists.intro b'
                  (And.intro data.left
                    (And.intro data.right.left
                      (And.intro sameAA'
                        (And.intro sameBB' data.right.right.right.right)))))

end BEDC.Derived.OptionUp
