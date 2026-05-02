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

theorem FieldSingletonClassifier_append_visible_left_absurd {p q h : BHist} :
    (FieldSingletonClassifier (append p (BHist.e0 q)) h -> False) ∧
      (FieldSingletonClassifier (append p (BHist.e1 q)) h -> False) := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.right
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.right

theorem FieldSingletonClassifier_append_visible_prefix_absurd {p q h : BHist} :
    (FieldSingletonClassifier (append (BHist.e0 p) q) h -> False) ∧
      (FieldSingletonClassifier (append (BHist.e1 p) q) h -> False) := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.left
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.left

theorem FieldSingletonClassifier_append_right_cancel_iff {P Q R : BHist} :
    FieldSingletonCarrier P ->
      (FieldSingletonClassifier (append Q P) (append R P) ↔ FieldSingletonClassifier Q R) := by
  intro carrierP
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.left
      (And.intro rightSplit.left
        (hsame_trans leftSplit.left (hsame_symm rightSplit.left)))
  · intro classified
    cases carrierP
    have leftCarrier : FieldSingletonCarrier (append Q BHist.Empty) :=
      hsame_trans (append_empty_right Q) classified.left
    have rightCarrier : FieldSingletonCarrier (append R BHist.Empty) :=
      hsame_trans (append_empty_right R) classified.right.left
    have sameAppend : hsame (append Q BHist.Empty) (append R BHist.Empty) :=
      hsame_trans (append_empty_right Q)
        (hsame_trans classified.right.right (hsame_symm (append_empty_right R)))
    exact And.intro leftCarrier (And.intro rightCarrier sameAppend)

end BEDC.Derived.FieldUp
