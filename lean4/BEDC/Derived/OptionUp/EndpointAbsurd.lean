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

end BEDC.Derived.OptionUp
