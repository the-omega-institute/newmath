import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def MatrixSingletonAddFold : List BHist -> BHist
  | [] => BHist.Empty
  | x :: xs => MatrixSingletonAdd x (MatrixSingletonAddFold xs)

def MatrixSingletonAddFoldSpineCarrier : List BHist -> Prop
  | [] => hsame BHist.Empty BHist.Empty
  | x :: xs => MatrixSingletonCarrier x ∧ MatrixSingletonAddFoldSpineCarrier xs

theorem MatrixSingletonAddFold_carrier_iff {xs : List BHist} :
    hsame (MatrixSingletonAddFold xs) BHist.Empty ↔
      MatrixSingletonAddFoldSpineCarrier xs := by
  induction xs with
  | nil =>
      constructor
      · intro _foldCarrier
        exact hsame_refl BHist.Empty
      · intro _spineCarrier
        exact hsame_refl BHist.Empty
  | cons x xs ih =>
      constructor
      · intro foldCarrier
        have parts := append_eq_empty_iff.mp foldCarrier
        exact And.intro parts.left (Iff.mp ih parts.right)
      · intro spineCarrier
        exact append_eq_empty_iff.mpr
          (And.intro spineCarrier.left (Iff.mpr ih spineCarrier.right))

theorem MatrixSingletonAddFold_continuation_result_iff {xs : List BHist} {h r : BHist} :
    Cont h (MatrixSingletonAddFold xs) r ->
      (MatrixSingletonCarrier r ↔
        MatrixSingletonCarrier h ∧ MatrixSingletonAddFoldSpineCarrier xs) := by
  intro continuation
  constructor
  · intro resultCarrier
    have emptyContinuation : Cont h (MatrixSingletonAddFold xs) BHist.Empty :=
      cont_result_hsame_transport continuation resultCarrier
    have endpoints := cont_empty_result_inversion emptyContinuation
    have foldCarrier : hsame (MatrixSingletonAddFold xs) BHist.Empty := endpoints.right
    exact And.intro endpoints.left (Iff.mp MatrixSingletonAddFold_carrier_iff foldCarrier)
  · intro carriers
    have foldCarrier : hsame (MatrixSingletonAddFold xs) BHist.Empty :=
      Iff.mpr MatrixSingletonAddFold_carrier_iff carriers.right
    exact
      cont_respects_hsame carriers.left foldCarrier continuation (cont_right_unit BHist.Empty)

theorem MatrixSingletonAddFold_visible_head_absurd {m : BHist} {xs : List BHist} :
    (hsame (MatrixSingletonAddFold (BHist.e0 m :: xs)) BHist.Empty -> False) ∧
      (hsame (MatrixSingletonAddFold (BHist.e1 m :: xs)) BHist.Empty -> False) := by
  constructor
  · intro foldEmpty
    exact not_hsame_e0_empty (append_eq_empty_iff.mp foldEmpty).left
  · intro foldEmpty
    exact not_hsame_e1_empty (append_eq_empty_iff.mp foldEmpty).left

theorem MatrixSingletonAddFold_append_carrier_iff {xs ys : List BHist} :
    hsame (MatrixSingletonAddFold (xs ++ ys)) BHist.Empty ↔
      MatrixSingletonAddFoldSpineCarrier xs ∧ MatrixSingletonAddFoldSpineCarrier ys := by
  induction xs with
  | nil =>
      constructor
      · intro foldCarrier
        exact And.intro (hsame_refl BHist.Empty)
          (Iff.mp MatrixSingletonAddFold_carrier_iff foldCarrier)
      · intro spineCarrier
        exact Iff.mpr MatrixSingletonAddFold_carrier_iff spineCarrier.right
  | cons x xs ih =>
      constructor
      · intro foldCarrier
        have parts := append_eq_empty_iff.mp foldCarrier
        have tailParts := Iff.mp ih parts.right
        exact And.intro (And.intro parts.left tailParts.left) tailParts.right
      · intro spineCarrier
        exact append_eq_empty_iff.mpr
          (And.intro spineCarrier.left.left
            (Iff.mpr ih (And.intro spineCarrier.left.right spineCarrier.right)))

theorem MatrixSingletonAddFold_append_visible_tail_absurd {xs : List BHist} {m : BHist} :
    (hsame (MatrixSingletonAddFold (xs ++ [BHist.e0 m])) BHist.Empty -> False) ∧
      (hsame (MatrixSingletonAddFold (xs ++ [BHist.e1 m])) BHist.Empty -> False) := by
  constructor
  · intro foldEmpty
    have spine :=
      Iff.mp (MatrixSingletonAddFold_append_carrier_iff (xs := xs) (ys := [BHist.e0 m]))
        foldEmpty
    exact not_hsame_e0_empty spine.right.left
  · intro foldEmpty
    have spine :=
      Iff.mp (MatrixSingletonAddFold_append_carrier_iff (xs := xs) (ys := [BHist.e1 m]))
        foldEmpty
    exact not_hsame_e1_empty spine.right.left

theorem MatrixSingletonAddFold_append_visible_middle_absurd {pref suffix : List BHist} {m : BHist} :
    (hsame (MatrixSingletonAddFold (pref ++ BHist.e0 m :: suffix)) BHist.Empty -> False) ∧
      (hsame (MatrixSingletonAddFold (pref ++ BHist.e1 m :: suffix)) BHist.Empty -> False) := by
  constructor
  · intro foldEmpty
    have spineParts :=
      Iff.mp
        (MatrixSingletonAddFold_append_carrier_iff
          (xs := pref) (ys := BHist.e0 m :: suffix))
        foldEmpty
    exact not_hsame_e0_empty spineParts.right.left
  · intro foldEmpty
    have spineParts :=
      Iff.mp
        (MatrixSingletonAddFold_append_carrier_iff
          (xs := pref) (ys := BHist.e1 m :: suffix))
        foldEmpty
    exact not_hsame_e1_empty spineParts.right.left

theorem MatrixSingletonAddFold_append_hsame {xs ys : List BHist} :
    hsame (MatrixSingletonAddFold (xs ++ ys))
      (append (MatrixSingletonAddFold xs) (MatrixSingletonAddFold ys)) := by
  induction xs with
  | nil =>
      exact (append_empty_left (MatrixSingletonAddFold ys)).symm
  | cons x xs ih =>
      exact (congrArg (append x) ih).trans
        (append_assoc x (MatrixSingletonAddFold xs) (MatrixSingletonAddFold ys)).symm

theorem MatrixSingletonAddFold_reverse_empty_append_hsame {xs : List BHist} :
    MatrixSingletonAddFoldSpineCarrier xs ->
      hsame (append (MatrixSingletonAddFold xs) BHist.Empty)
        (append (MatrixSingletonAddFold xs.reverse) BHist.Empty) := by
  intro carrier
  have reverseCarrier :
      ∀ {ys : List BHist}, MatrixSingletonAddFoldSpineCarrier ys ->
        MatrixSingletonAddFoldSpineCarrier ys.reverse := by
    intro ys ysCarrier
    have reverseAuxCarrier :
        ∀ {tail acc : List BHist}, MatrixSingletonAddFoldSpineCarrier tail ->
          MatrixSingletonAddFoldSpineCarrier acc ->
            MatrixSingletonAddFoldSpineCarrier (List.reverseAux tail acc) := by
      intro tail acc tailCarrier accCarrier
      induction tail generalizing acc with
      | nil =>
          exact accCarrier
      | cons y tail ih =>
          exact ih tailCarrier.right (And.intro tailCarrier.left accCarrier)
    exact reverseAuxCarrier ysCarrier (hsame_refl BHist.Empty)
  have leftEmpty : hsame (MatrixSingletonAddFold xs) BHist.Empty :=
    Iff.mpr MatrixSingletonAddFold_carrier_iff carrier
  have rightEmpty : hsame (MatrixSingletonAddFold xs.reverse) BHist.Empty :=
    Iff.mpr MatrixSingletonAddFold_carrier_iff (reverseCarrier carrier)
  exact hsame_trans leftEmpty (hsame_symm rightEmpty)

theorem MatrixSingletonAddFold_append_display_classifier_iff {xs ys : List BHist} :
    MatrixSingletonClassifier (MatrixSingletonAddFold (xs ++ ys))
      (append (MatrixSingletonAddFold xs) (MatrixSingletonAddFold ys)) ↔
        MatrixSingletonAddFoldSpineCarrier xs ∧ MatrixSingletonAddFoldSpineCarrier ys := by
  constructor
  · intro classified
    exact Iff.mp MatrixSingletonAddFold_append_carrier_iff classified.left
  · intro spine
    have foldedCarrier : MatrixSingletonCarrier (MatrixSingletonAddFold (xs ++ ys)) :=
      Iff.mpr MatrixSingletonAddFold_append_carrier_iff spine
    have displayedCarrier :
        MatrixSingletonCarrier (append (MatrixSingletonAddFold xs) (MatrixSingletonAddFold ys)) :=
      append_eq_empty_iff.mpr
        (And.intro
          (Iff.mpr MatrixSingletonAddFold_carrier_iff spine.left)
          (Iff.mpr MatrixSingletonAddFold_carrier_iff spine.right))
    exact And.intro foldedCarrier
      (And.intro displayedCarrier MatrixSingletonAddFold_append_hsame)

theorem MatrixSingletonAddFold_reverse_carrier_readback {xs : List BHist} :
    MatrixSingletonAddFoldSpineCarrier xs ->
      MatrixSingletonCarrier (MatrixSingletonAddFold xs.reverse) ∧
        hsame (MatrixSingletonAddFold xs) (MatrixSingletonAddFold xs.reverse) := by
  intro carrier
  have reverseCarrier :
      ∀ {ys : List BHist}, MatrixSingletonAddFoldSpineCarrier ys ->
        MatrixSingletonAddFoldSpineCarrier ys.reverse := by
    intro ys ysCarrier
    have reverseAuxCarrier :
        ∀ {tail acc : List BHist}, MatrixSingletonAddFoldSpineCarrier tail ->
          MatrixSingletonAddFoldSpineCarrier acc ->
            MatrixSingletonAddFoldSpineCarrier (List.reverseAux tail acc) := by
      intro tail acc tailCarrier accCarrier
      induction tail generalizing acc with
      | nil =>
          exact accCarrier
      | cons y tail ih =>
          exact ih tailCarrier.right (And.intro tailCarrier.left accCarrier)
    exact reverseAuxCarrier ysCarrier (hsame_refl BHist.Empty)
  have leftCarrier : MatrixSingletonCarrier (MatrixSingletonAddFold xs) :=
    Iff.mpr MatrixSingletonAddFold_carrier_iff carrier
  have rightCarrier : MatrixSingletonCarrier (MatrixSingletonAddFold xs.reverse) :=
    Iff.mpr MatrixSingletonAddFold_carrier_iff (reverseCarrier carrier)
  exact And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier))

theorem MatrixSingletonAddFold_append_continuation_classifier
    {xs ys : List BHist} {r : BHist} :
    MatrixSingletonAddFoldSpineCarrier xs ->
      MatrixSingletonAddFoldSpineCarrier ys ->
        Cont (MatrixSingletonAddFold xs) (MatrixSingletonAddFold ys) r ->
          MatrixSingletonClassifier (MatrixSingletonAddFold (xs ++ ys)) r := by
  intro xsCarrier ysCarrier continuation
  have displayedClassifier :
      MatrixSingletonClassifier (MatrixSingletonAddFold (xs ++ ys))
        (append (MatrixSingletonAddFold xs) (MatrixSingletonAddFold ys)) :=
    Iff.mpr MatrixSingletonAddFold_append_display_classifier_iff
      (And.intro xsCarrier ysCarrier)
  have sameResult : hsame (append (MatrixSingletonAddFold xs) (MatrixSingletonAddFold ys)) r :=
    cont_deterministic (cont_intro rfl) continuation
  exact And.intro displayedClassifier.left
    (And.intro
      (hsame_trans (hsame_symm sameResult) displayedClassifier.right.left)
      (hsame_trans displayedClassifier.right.right sameResult))

end BEDC.Derived.MatrixUp
