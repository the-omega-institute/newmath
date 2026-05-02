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

theorem OptionHistoryClassifier_empty_endpoint_equivalence {source : BHist -> Prop}
    {h k : BHist} :
    OptionHistoryClassifier source h k -> (hsame h BHist.Empty <-> hsame k BHist.Empty) := by
  intro classifier
  cases classifier with
  | intro _ rest =>
      cases rest with
      | intro _ sameHK =>
          constructor
          · intro sameHEmpty
            exact hsame_trans (hsame_symm sameHK) sameHEmpty
          · intro sameKEmpty
            exact hsame_trans sameHK sameKEmpty

end BEDC.Derived.OptionUp
