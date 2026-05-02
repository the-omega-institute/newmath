import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionHistoryClassifier_empty_right_iff {source : BHist → Prop} {h : BHist} :
    OptionHistoryClassifier source h BHist.Empty ↔ hsame h BHist.Empty := by
  constructor
  · intro classifier
    cases classifier with
    | intro _ rest =>
        cases rest with
        | intro _ same =>
            exact same
  · intro same
    constructor
    · exact Or.inl same
    · constructor
      · exact Or.inl (hsame_refl BHist.Empty)
      · exact same

end BEDC.Derived.OptionUp
