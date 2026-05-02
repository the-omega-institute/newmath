import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_empty_visible_exclusion {S : BHist → Prop}
    {Rel : BHist → BHist → Prop} {h k a b : BHist} :
    TaggedOptionHistoryClassifier S Rel h k →
      (hsame h BHist.Empty → hsame k (BHist.e1 b) → False) ∧
        (hsame k BHist.Empty → hsame h (BHist.e1 a) → False) := by
  intro classifier
  constructor
  · intro sameHEmpty sameKPresent
    cases classifier with
    | inl absentPair =>
        exact not_hsame_emp_e1 (hsame_trans (hsame_symm absentPair.right) sameKPresent)
    | inr presentPair =>
        cases presentPair with
        | intro sourcePayload targetData =>
            cases targetData with
            | intro _targetPayload data =>
                cases data with
                | intro _sourceIn rest =>
                    cases rest with
                    | intro _targetIn rest =>
                        cases rest with
                        | intro sameHPresent _rest =>
                            exact
                              not_hsame_emp_e1
                                (hsame_trans (hsame_symm sameHEmpty) sameHPresent)
  · intro sameKEmpty sameHPresent
    cases classifier with
    | inl absentPair =>
        exact not_hsame_emp_e1 (hsame_trans (hsame_symm absentPair.left) sameHPresent)
    | inr presentPair =>
        cases presentPair with
        | intro _sourcePayload targetData =>
            cases targetData with
            | intro _targetPayload data =>
                cases data with
                | intro _sourceIn rest =>
                    cases rest with
                    | intro _targetIn rest =>
                        cases rest with
                        | intro _sameHPresent rest =>
                            cases rest with
                            | intro sameKPresent _rel =>
                                exact
                                  not_hsame_emp_e1
                                    (hsame_trans (hsame_symm sameKEmpty) sameKPresent)

end BEDC.Derived.OptionUp
