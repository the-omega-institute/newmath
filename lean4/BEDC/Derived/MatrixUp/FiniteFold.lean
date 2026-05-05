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

end BEDC.Derived.MatrixUp
