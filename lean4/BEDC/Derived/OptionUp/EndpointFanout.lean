import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_left_present_endpoint_fanout {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k r a : BHist} :
    TaggedOptionHistoryClassifier S Rel h k -> TaggedOptionHistoryClassifier S Rel h r ->
      hsame h (BHist.e1 a) ->
        (exists b : BHist, S b /\ hsame k (BHist.e1 b)) /\
          (exists c : BHist, S c /\ hsame r (BHist.e1 c)) := by
  intro left right sameHPresent
  constructor
  · cases left with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameHPresent))
    | inr present =>
        cases present with
        | intro _source restSource =>
            cases restSource with
            | intro target data =>
                exact Exists.intro target (And.intro data.right.left data.right.right.right.left)
  · cases right with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameHPresent))
    | inr present =>
        cases present with
        | intro _source restSource =>
            cases restSource with
            | intro target data =>
                exact Exists.intro target (And.intro data.right.left data.right.right.right.left)

theorem TaggedOptionHistoryClassifier_right_present_endpoint_fanout {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k r a : BHist} :
    TaggedOptionHistoryClassifier S Rel h k -> TaggedOptionHistoryClassifier S Rel r k ->
      hsame k (BHist.e1 a) ->
        (exists b : BHist, S b /\ hsame h (BHist.e1 b)) /\
          (exists c : BHist, S c /\ hsame r (BHist.e1 c)) := by
  intro left right sameKPresent
  constructor
  · cases left with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.right) sameKPresent))
    | inr present =>
        cases present with
        | intro source restSource =>
            cases restSource with
            | intro _target data =>
                exact Exists.intro source (And.intro data.left data.right.right.left)
  · cases right with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.right) sameKPresent))
    | inr present =>
        cases present with
        | intro source restSource =>
            cases restSource with
            | intro _target data =>
                exact Exists.intro source (And.intro data.left data.right.right.left)

end BEDC.Derived.OptionUp
