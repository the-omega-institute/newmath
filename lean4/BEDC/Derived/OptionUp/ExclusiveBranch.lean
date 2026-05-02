import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionHistoryClassifier_exclusive_branch_iff {source : BHist -> Prop}
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {h k : BHist} :
    OptionHistoryClassifier source h k ↔
      (hsame h BHist.Empty ∧ hsame k BHist.Empty) ∨
        (source h ∧ source k ∧ hsame h k) := by
  constructor
  · intro classifier
    cases classifier with
    | intro carrierH rest =>
        cases rest with
        | intro carrierK sameHK =>
            cases carrierH with
            | inl sameHEmpty =>
                cases carrierK with
                | inl sameKEmpty =>
                    exact Or.inl (And.intro sameHEmpty sameKEmpty)
                | inr sourceK =>
                    exact False.elim
                      (sourceExcludesEmpty k sourceK
                        (hsame_trans (hsame_symm sameHK) sameHEmpty))
            | inr sourceH =>
                cases carrierK with
                | inl sameKEmpty =>
                    exact False.elim
                      (sourceExcludesEmpty h sourceH (hsame_trans sameHK sameKEmpty))
                | inr sourceK =>
                    exact Or.inr (And.intro sourceH (And.intro sourceK sameHK))
  · intro branches
    cases branches with
    | inl emptyPair =>
        exact
          And.intro (Or.inl emptyPair.left)
            (And.intro (Or.inl emptyPair.right)
              (hsame_trans emptyPair.left (hsame_symm emptyPair.right)))
    | inr sourcePair =>
        exact
          And.intro (Or.inr sourcePair.left)
            (And.intro (Or.inr sourcePair.right.left) sourcePair.right.right)

theorem OptionHistoryClassifier_source_branch_iff {source : BHist -> Prop}
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {h k : BHist} :
    OptionHistoryClassifier source h k -> (source h <-> source k) := by
  intro classifier
  constructor
  · intro sourceH
    cases classifier with
    | intro _carrierH rest =>
        cases rest with
        | intro carrierK sameHK =>
            cases carrierK with
            | inl sameKEmpty =>
                exact False.elim (sourceExcludesEmpty h sourceH (hsame_trans sameHK sameKEmpty))
            | inr sourceK =>
                exact sourceK
  · intro sourceK
    cases classifier with
    | intro carrierH rest =>
        cases rest with
        | intro _carrierK sameHK =>
            cases carrierH with
            | inl sameHEmpty =>
                exact False.elim
                  (sourceExcludesEmpty k sourceK (hsame_trans (hsame_symm sameHK) sameHEmpty))
            | inr sourceH =>
                exact sourceH

end BEDC.Derived.OptionUp
