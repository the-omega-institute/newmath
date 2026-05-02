import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_e0_endpoint_absurd {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {tail h : BHist} :
    (TaggedOptionHistoryClassifier S Rel (BHist.e0 tail) h -> False) /\
      (TaggedOptionHistoryClassifier S Rel h (BHist.e0 tail) -> False) := by
  constructor
  · intro classifier
    cases classifier with
    | inl absentPair =>
        exact not_hsame_e0_empty absentPair.left
    | inr presentPair =>
        cases presentPair with
        | intro a restA =>
            cases restA with
            | intro _b data =>
                cases data with
                | intro _sourceA rest =>
                    cases rest with
                    | intro _sourceB rest =>
                        cases rest with
                        | intro sameLeft _rest =>
                            exact not_hsame_e0_e1 sameLeft
  · intro classifier
    cases classifier with
    | inl absentPair =>
        exact not_hsame_e0_empty absentPair.right
    | inr presentPair =>
        cases presentPair with
        | intro _a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro _sourceA rest =>
                    cases rest with
                    | intro _sourceB rest =>
                        cases rest with
                        | intro _sameLeft rest =>
                            cases rest with
                            | intro sameRight _rel =>
                                exact not_hsame_e0_e1 sameRight

theorem TaggedOptionHistoryClassifier_zero_endpoint_exclusion {S : BHist → Prop}
    {Rel : BHist → BHist → Prop} {h k tail : BHist} :
    TaggedOptionHistoryClassifier S Rel h k →
      (hsame h (BHist.e0 tail) → False) ∧ (hsame k (BHist.e0 tail) → False) := by
  intro classifier
  constructor
  · intro sameLeftZero
    cases classifier with
    | inl absentPair =>
        exact
          not_hsame_e0_empty
            (hsame_trans (hsame_symm sameLeftZero) absentPair.left)
    | inr presentPair =>
        cases presentPair with
        | intro a restA =>
            cases restA with
            | intro _b data =>
                cases data with
                | intro _sourceA rest =>
                    cases rest with
                    | intro _sourceB rest =>
                        cases rest with
                        | intro sameLeftPresent _rest =>
                            exact
                              not_hsame_e0_e1
                                (hsame_trans (hsame_symm sameLeftZero) sameLeftPresent)
  · intro sameRightZero
    cases classifier with
    | inl absentPair =>
        exact
          not_hsame_e0_empty
            (hsame_trans (hsame_symm sameRightZero) absentPair.right)
    | inr presentPair =>
        cases presentPair with
        | intro _a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro _sourceA rest =>
                    cases rest with
                    | intro _sourceB rest =>
                        cases rest with
                        | intro _sameLeft rest =>
                            cases rest with
                            | intro sameRightPresent _rel =>
                                exact
                                  not_hsame_e0_e1
                                    (hsame_trans (hsame_symm sameRightZero)
                                      sameRightPresent)

end BEDC.Derived.OptionUp
