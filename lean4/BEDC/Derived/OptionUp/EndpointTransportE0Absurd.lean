import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_endpoint_transport_e0_absurd {S : BHist → Prop}
    {Rel : BHist → BHist → Prop} {h k tail : BHist} :
    TaggedOptionHistoryClassifier S Rel h k →
      (hsame h (BHist.e0 tail) → False) ∧ (hsame k (BHist.e0 tail) → False) := by
  intro classifier
  constructor
  · intro sameH
    cases classifier with
    | inl absentPair =>
        exact not_hsame_e0_empty (hsame_trans (hsame_symm sameH) absentPair.left)
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
                        | intro sameHPresent _rest =>
                            exact not_hsame_e0_e1 (hsame_trans (hsame_symm sameH) sameHPresent)
  · intro sameK
    cases classifier with
    | inl absentPair =>
        exact not_hsame_e0_empty (hsame_trans (hsame_symm sameK) absentPair.right)
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
                        | intro _sameHPresent rest =>
                            cases rest with
                            | intro sameKPresent _rel =>
                                exact not_hsame_e0_e1
                                  (hsame_trans (hsame_symm sameK) sameKPresent)

end BEDC.Derived.OptionUp
