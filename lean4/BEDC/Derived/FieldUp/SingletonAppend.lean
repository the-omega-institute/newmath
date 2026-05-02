import BEDC.Derived.FieldUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem fieldSingletonEmptyClassifier_append_split_empty_iff {p q h : BHist} :
    fieldSingletonEmptyClassifier (append p q) h ↔
      hsame p BHist.Empty ∧ hsame q BHist.Empty ∧ fieldSingletonEmptyCarrier h := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    exact And.intro emptyParts.left (And.intro emptyParts.right classified.right.left)
  · intro split
    have appendEmpty : hsame (append p q) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro split.left split.right.left)
    exact And.intro appendEmpty
      (And.intro split.right.right (hsame_trans appendEmpty (hsame_symm split.right.right)))

end BEDC.Derived.FieldUp
