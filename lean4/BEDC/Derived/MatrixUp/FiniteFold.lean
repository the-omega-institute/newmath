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

end BEDC.Derived.MatrixUp
