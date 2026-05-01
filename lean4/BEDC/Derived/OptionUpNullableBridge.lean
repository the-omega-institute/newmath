import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

def TaggedOptionToNullableBridge (S : BHist -> Prop) (Rel : BHist -> BHist -> Prop) : Prop :=
  (forall a h : BHist, S a -> hsame h (BHist.e1 a) -> S h) /\
    (forall a b : BHist, S a -> S b -> Rel a b -> hsame a b)

theorem TaggedOptionToNullableBridge_descent {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} :
    TaggedOptionToNullableBridge S Rel ->
      (forall h : BHist, TaggedOptionHistoryCarrier S h -> OptionHistoryCarrier S h) /\
        (forall h k : BHist,
          TaggedOptionHistoryClassifier S Rel h k -> OptionHistoryClassifier S h k) := by
  intro bridge
  cases bridge with
  | intro presentClosure relSound =>
      constructor
      · intro h carrier
        cases carrier with
        | inl absent =>
            exact Or.inl absent
        | inr present =>
            cases present with
            | intro a data =>
                cases data with
                | intro sourceA samePresent =>
                    exact Or.inr (presentClosure a h sourceA samePresent)
      · intro h k classifier
        cases classifier with
        | inl absent =>
            constructor
            · exact Or.inl absent.left
            · constructor
              · exact Or.inl absent.right
              · exact hsame_trans absent.left (hsame_symm absent.right)
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
                                | intro sameK relAB =>
                                    have sameAB : hsame a b :=
                                      relSound a b sourceA sourceB relAB
                                    constructor
                                    · exact Or.inr (presentClosure a h sourceA sameH)
                                    · constructor
                                      · exact Or.inr (presentClosure b k sourceB sameK)
                                      · exact hsame_trans sameH
                                          (hsame_trans (hsame_e1_congr sameAB)
                                            (hsame_symm sameK))

end BEDC.Derived.OptionUp
