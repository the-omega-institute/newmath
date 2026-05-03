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

theorem fieldSingletonEmptyClassifier_append_right_cancel_iff {P Q R : BHist} :
    fieldSingletonEmptyCarrier P ->
      (fieldSingletonEmptyClassifier (append Q P) (append R P) ↔
        fieldSingletonEmptyClassifier Q R) := by
  intro carrierP
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.left
      (And.intro rightSplit.left
        (hsame_trans leftSplit.left (hsame_symm rightSplit.left)))
  · intro classified
    have leftCarrier : fieldSingletonEmptyCarrier (append Q P) :=
      append_eq_empty_iff.mpr (And.intro classified.left carrierP)
    have rightCarrier : fieldSingletonEmptyCarrier (append R P) :=
      append_eq_empty_iff.mpr (And.intro classified.right.left carrierP)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

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

theorem fieldSingletonEmptyNonZero_append_visible_right {p q : BHist} :
    fieldSingletonEmptyNonZero (append p (BHist.e0 q)) ∧
      fieldSingletonEmptyNonZero (append p (BHist.e1 q)) := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.right
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.right

theorem fieldSingletonEmptyNonZero_append_context_cancel_iff {L R Q : BHist} :
    fieldSingletonEmptyCarrier L -> fieldSingletonEmptyCarrier R ->
      (fieldSingletonEmptyNonZero (append L (append Q R)) <->
        fieldSingletonEmptyNonZero Q) := by
  intro carrierL carrierR
  constructor
  · intro contextNonzero
    intro qClassified
    have innerCarrier : fieldSingletonEmptyCarrier (append Q R) :=
      append_eq_empty_iff.mpr (And.intro qClassified.left carrierR)
    have contextCarrier : fieldSingletonEmptyCarrier (append L (append Q R)) :=
      append_eq_empty_iff.mpr (And.intro carrierL innerCarrier)
    exact contextNonzero
      (And.intro contextCarrier
        (And.intro (hsame_refl BHist.Empty) contextCarrier))
  · intro qNonzero
    intro contextClassified
    have outerSplit := append_eq_empty_iff.mp contextClassified.left
    have innerSplit := append_eq_empty_iff.mp outerSplit.right
    exact qNonzero
      (And.intro innerSplit.left
        (And.intro (hsame_refl BHist.Empty) innerSplit.left))

theorem fieldSingletonEmptyNonZero_append_source_or_tail {P Q : BHist} :
    fieldSingletonEmptyNonZero (append P Q) ->
      fieldSingletonEmptyNonZero P ∨ fieldSingletonEmptyNonZero Q := by
  intro appendNonzero
  cases P with
  | Empty =>
      right
      intro qClassified
      apply appendNonzero
      have appendCarrier : fieldSingletonEmptyCarrier (append BHist.Empty Q) :=
        hsame_trans (append_empty_left Q) qClassified.left
      exact And.intro appendCarrier
        (And.intro (hsame_refl BHist.Empty) appendCarrier)
  | e0 p =>
      left
      intro pClassified
      exact not_hsame_e0_empty pClassified.left
  | e1 p =>
      left
      intro pClassified
      exact not_hsame_e1_empty pClassified.left

theorem fieldSingletonEmptyNonZero_append_split_iff {L Q : BHist} :
    fieldSingletonEmptyNonZero (append L Q) ↔
      fieldSingletonEmptyNonZero L ∨ fieldSingletonEmptyNonZero Q := by
  constructor
  · intro appendNonzero
    cases L with
    | Empty =>
        right
        intro classifiedQ
        have appendEmpty : hsame (append BHist.Empty Q) BHist.Empty :=
          hsame_trans (append_empty_left Q) classifiedQ.left
        exact appendNonzero
          (And.intro appendEmpty (And.intro (hsame_refl BHist.Empty) appendEmpty))
    | e0 l =>
        left
        intro classifiedL
        exact not_hsame_e0_empty classifiedL.left
    | e1 l =>
        left
        intro classifiedL
        exact not_hsame_e1_empty classifiedL.left
  · intro split classifiedAppend
    have emptyParts := append_eq_empty_iff.mp classifiedAppend.left
    cases split with
    | inl leftNonzero =>
        exact leftNonzero
          (And.intro emptyParts.left (And.intro (hsame_refl BHist.Empty) emptyParts.left))
    | inr rightNonzero =>
        exact rightNonzero
          (And.intro emptyParts.right (And.intro (hsame_refl BHist.Empty) emptyParts.right))

theorem FieldSingletonCarrier_append_visible_head_absurd {h k : BHist} :
    (FieldSingletonCarrier (append (BHist.e0 h) k) -> False) ∧
      (FieldSingletonCarrier (append (BHist.e1 h) k) -> False) := by
  constructor
  · intro carrier
    have emptyParts := append_eq_empty_iff.mp carrier
    cases emptyParts.left
  · intro carrier
    have emptyParts := append_eq_empty_iff.mp carrier
    cases emptyParts.left

theorem FieldSingletonCarrier_append_visible_tail_absurd {p q : BHist} :
    (FieldSingletonCarrier (append p (BHist.e0 q)) -> False) ∧
      (FieldSingletonCarrier (append p (BHist.e1 q)) -> False) := by
  constructor
  · intro carrier
    have emptyParts := append_eq_empty_iff.mp carrier
    exact not_hsame_e0_empty emptyParts.right
  · intro carrier
    have emptyParts := append_eq_empty_iff.mp carrier
    exact not_hsame_e1_empty emptyParts.right

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

theorem FieldSingletonClassifier_append_left_cancel_iff {P Q R : BHist} :
    FieldSingletonCarrier P ->
      (FieldSingletonClassifier (append P Q) (append P R) ↔ FieldSingletonClassifier Q R) := by
  intro carrierP
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.right
      (And.intro rightSplit.right
        (hsame_trans leftSplit.right (hsame_symm rightSplit.right)))
  · intro classified
    have leftCarrier : FieldSingletonCarrier (append P Q) :=
      append_eq_empty_iff.mpr (And.intro carrierP classified.left)
    have rightCarrier : FieldSingletonCarrier (append P R) :=
      append_eq_empty_iff.mpr (And.intro carrierP classified.right.left)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

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

theorem FieldSingletonCarrier_append_right_cancel_iff {P Q : BHist} :
    FieldSingletonCarrier P ->
      (FieldSingletonCarrier (append Q P) <-> FieldSingletonCarrier Q) := by
  intro carrierP
  constructor
  · intro carrierAppend
    exact (append_eq_empty_iff.mp carrierAppend).left
  · intro carrierQ
    exact append_eq_empty_iff.mpr (And.intro carrierQ carrierP)

theorem FieldSingletonCarrier_append_context_empty_iff {L R h : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      (FieldSingletonCarrier (append L (append h R)) ↔ FieldSingletonCarrier h) := by
  intro carrierL carrierR
  constructor
  · intro carrier
    have outerSplit := append_eq_empty_iff.mp carrier
    have innerSplit := append_eq_empty_iff.mp outerSplit.right
    exact innerSplit.left
  · intro carrier
    have innerCarrier : FieldSingletonCarrier (append h R) :=
      append_eq_empty_iff.mpr (And.intro carrier carrierR)
    exact append_eq_empty_iff.mpr (And.intro carrierL innerCarrier)

theorem FieldSingletonNonZero_append_context_cancel_iff {L R Q : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      (FieldSingletonNonZero (append L (append Q R)) <-> FieldSingletonNonZero Q) := by
  intro carrierL carrierR
  cases carrierL
  cases carrierR
  have contextSame : hsame (append BHist.Empty (append Q BHist.Empty)) Q :=
    hsame_trans (append_empty_left (append Q BHist.Empty)) (append_empty_right Q)
  constructor
  · intro contextNonZero
    exact And.intro
      (append_eq_empty_iff.mp (append_eq_empty_iff.mp contextNonZero.left).right).left
      (hsame_trans (hsame_symm contextSame) contextNonZero.right)
  · intro nonZero
    exact And.intro
      (append_eq_empty_iff.mpr
        (And.intro (hsame_refl BHist.Empty)
          (append_eq_empty_iff.mpr (And.intro nonZero.left (hsame_refl BHist.Empty)))))
      (hsame_trans contextSame nonZero.right)

theorem FieldSingletonClassifier_append_context_empty_iff {L R h k : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      (FieldSingletonClassifier (append L h) (append k R) ↔ FieldSingletonClassifier h k) := by
  intro carrierL carrierR
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.right
      (And.intro rightSplit.left (hsame_trans leftSplit.right (hsame_symm rightSplit.left)))
  · intro classified
    have leftCarrier : FieldSingletonCarrier (append L h) :=
      append_eq_empty_iff.mpr (And.intro carrierL classified.left)
    have rightCarrier : FieldSingletonCarrier (append k R) :=
      append_eq_empty_iff.mpr (And.intro classified.right.left carrierR)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

theorem FieldSingletonClassifier_append_endpoint_split_iff {L Q R S : BHist} :
    FieldSingletonClassifier (append L Q) (append R S) <->
      FieldSingletonCarrier L /\ FieldSingletonCarrier Q /\
        FieldSingletonCarrier R /\ FieldSingletonCarrier S := by
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.left
      (And.intro leftSplit.right (And.intro rightSplit.left rightSplit.right))
  · intro split
    have leftCarrier : FieldSingletonCarrier (append L Q) :=
      append_eq_empty_iff.mpr (And.intro split.left split.right.left)
    have rightCarrier : FieldSingletonCarrier (append R S) :=
      append_eq_empty_iff.mpr (And.intro split.right.right.left split.right.right.right)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

end BEDC.Derived.FieldUp
