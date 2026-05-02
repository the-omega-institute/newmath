import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_option_history_classifier {S : BHist -> Prop}
    {h k : BHist} :
    TaggedOptionHistoryClassifier S hsame h k ->
      OptionHistoryClassifier (TaggedOptionHistoryCarrier S) h k := by
  intro classifier
  cases classifier with
  | inl absent =>
      exact And.intro (Or.inl absent.left)
        (And.intro (Or.inl absent.right) (hsame_trans absent.left (hsame_symm absent.right)))
  | inr present =>
      cases present with
      | intro a restA =>
          cases restA with
          | intro b data =>
              exact And.intro
                (Or.inr (Or.inr (Exists.intro a (And.intro data.left data.right.right.left))))
                (And.intro
                  (Or.inr
                    (Or.inr
                      (Exists.intro b (And.intro data.right.left data.right.right.right.left))))
                  (hsame_trans data.right.right.left
                    (hsame_trans (hsame_e1_congr data.right.right.right.right)
                      (hsame_symm data.right.right.right.left))))

end BEDC.Derived.OptionUp
