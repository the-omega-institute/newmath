import BEDC.Derived.MatrixUp
import BEDC.Derived.ListUp

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

theorem MatrixSingletonAddFold_cont_visible_head_result_nonempty {m : BHist} {xs : List BHist}
    {h r : BHist} :
    (Cont h (MatrixSingletonAddFold (BHist.e0 m :: xs)) r ->
      hsame r BHist.Empty -> False) ∧
      (Cont h (MatrixSingletonAddFold (BHist.e1 m :: xs)) r ->
        hsame r BHist.Empty -> False) := by
  constructor
  · intro continuation resultEmpty
    have endpoints :=
      cont_empty_result_inversion (cont_result_hsame_transport continuation resultEmpty)
    exact MatrixSingletonAddFold_visible_head_absurd.left endpoints.right
  · intro continuation resultEmpty
    have endpoints :=
      cont_empty_result_inversion (cont_result_hsame_transport continuation resultEmpty)
    exact MatrixSingletonAddFold_visible_head_absurd.right endpoints.right

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

theorem MatrixSingletonAddFold_reverse_carrier_iff {xs : List BHist} :
    hsame (MatrixSingletonAddFold xs.reverse) BHist.Empty <->
      hsame (MatrixSingletonAddFold xs) BHist.Empty := by
  have reverseAuxSpineCarrier :
      ∀ tail acc : List BHist,
        MatrixSingletonAddFoldSpineCarrier (List.reverseAux tail acc) <->
          MatrixSingletonAddFoldSpineCarrier tail ∧
            MatrixSingletonAddFoldSpineCarrier acc := by
    intro tail
    induction tail with
    | nil =>
        intro acc
        constructor
        · intro accCarrier
          exact And.intro (hsame_refl BHist.Empty) accCarrier
        · intro parts
          exact parts.right
    | cons y tail ih =>
        intro acc
        constructor
        · intro reversedCarrier
          have parts := Iff.mp (ih (y :: acc)) reversedCarrier
          exact And.intro (And.intro parts.right.left parts.left) parts.right.right
        · intro parts
          exact Iff.mpr (ih (y :: acc))
            (And.intro parts.left.right (And.intro parts.left.left parts.right))
  constructor
  · intro reverseFoldCarrier
    have reverseSpine :
        MatrixSingletonAddFoldSpineCarrier xs.reverse :=
      Iff.mp MatrixSingletonAddFold_carrier_iff reverseFoldCarrier
    have spineParts := Iff.mp (reverseAuxSpineCarrier xs []) reverseSpine
    exact Iff.mpr MatrixSingletonAddFold_carrier_iff spineParts.left
  · intro foldCarrier
    have spine : MatrixSingletonAddFoldSpineCarrier xs :=
      Iff.mp MatrixSingletonAddFold_carrier_iff foldCarrier
    have reverseSpine :
        MatrixSingletonAddFoldSpineCarrier xs.reverse :=
      Iff.mpr (reverseAuxSpineCarrier xs [])
        (And.intro spine (hsame_refl BHist.Empty))
    exact Iff.mpr MatrixSingletonAddFold_carrier_iff reverseSpine

theorem MatrixSingletonAddFold_reverse_continuation_result_iff {xs : List BHist} {h r : BHist} :
    Cont h (MatrixSingletonAddFold xs.reverse) r ->
      (MatrixSingletonCarrier r <->
        MatrixSingletonCarrier h ∧ hsame (MatrixSingletonAddFold xs) BHist.Empty) := by
  intro continuation
  have reverseResult :=
    MatrixSingletonAddFold_continuation_result_iff
      (xs := xs.reverse) (h := h) (r := r) continuation
  constructor
  · intro resultCarrier
    have reverseData := Iff.mp reverseResult resultCarrier
    have reverseFoldCarrier : hsame (MatrixSingletonAddFold xs.reverse) BHist.Empty :=
      Iff.mpr MatrixSingletonAddFold_carrier_iff reverseData.right
    exact And.intro reverseData.left
      (Iff.mp MatrixSingletonAddFold_reverse_carrier_iff reverseFoldCarrier)
  · intro data
    have reverseFoldCarrier : hsame (MatrixSingletonAddFold xs.reverse) BHist.Empty :=
      Iff.mpr MatrixSingletonAddFold_reverse_carrier_iff data.right
    have reverseSpine : MatrixSingletonAddFoldSpineCarrier xs.reverse :=
      Iff.mp MatrixSingletonAddFold_carrier_iff reverseFoldCarrier
    exact Iff.mpr reverseResult (And.intro data.left reverseSpine)

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

theorem MatrixSingletonAddFold_continuation_append_display_classifier_iff
    {xs ys : List BHist} {h r : BHist} :
    Cont h (append (MatrixSingletonAddFold xs) (MatrixSingletonAddFold ys)) r ->
      (MatrixSingletonCarrier r ↔
        MatrixSingletonCarrier h ∧ MatrixSingletonAddFoldSpineCarrier xs ∧
          MatrixSingletonAddFoldSpineCarrier ys) := by
  intro continuation
  constructor
  · intro resultCarrier
    have emptyContinuation :
        Cont h (append (MatrixSingletonAddFold xs) (MatrixSingletonAddFold ys))
          BHist.Empty :=
      cont_result_hsame_transport continuation resultCarrier
    have endpoints := cont_empty_result_inversion emptyContinuation
    have foldEndpoints :=
      append_eq_empty_iff.mp endpoints.right
    exact And.intro endpoints.left
      (And.intro
        (Iff.mp MatrixSingletonAddFold_carrier_iff foldEndpoints.left)
        (Iff.mp MatrixSingletonAddFold_carrier_iff foldEndpoints.right))
  · intro carriers
    have leftFoldCarrier : MatrixSingletonCarrier (MatrixSingletonAddFold xs) :=
      Iff.mpr MatrixSingletonAddFold_carrier_iff carriers.right.left
    have rightFoldCarrier : MatrixSingletonCarrier (MatrixSingletonAddFold ys) :=
      Iff.mpr MatrixSingletonAddFold_carrier_iff carriers.right.right
    have appendCarrier :
        MatrixSingletonCarrier (append (MatrixSingletonAddFold xs) (MatrixSingletonAddFold ys)) :=
      append_eq_empty_iff.mpr (And.intro leftFoldCarrier rightFoldCarrier)
    exact
      cont_respects_hsame carriers.left appendCarrier continuation (cont_right_unit BHist.Empty)

theorem MatrixSingletonAddFold_append_continuation_result_iff {xs ys : List BHist} {h r : BHist} :
    Cont h (MatrixSingletonAddFold (xs ++ ys)) r ->
      (MatrixSingletonCarrier r ↔
        MatrixSingletonCarrier h ∧ MatrixSingletonAddFoldSpineCarrier xs ∧
          MatrixSingletonAddFoldSpineCarrier ys) := by
  intro continuation
  constructor
  · intro resultCarrier
    have carrierData :=
      Iff.mp (MatrixSingletonAddFold_continuation_result_iff continuation) resultCarrier
    have foldEmpty : hsame (MatrixSingletonAddFold (xs ++ ys)) BHist.Empty :=
      Iff.mpr MatrixSingletonAddFold_carrier_iff carrierData.right
    have appendData :=
      Iff.mp MatrixSingletonAddFold_append_carrier_iff foldEmpty
    exact And.intro carrierData.left (And.intro appendData.left appendData.right)
  · intro carrierData
    have foldEmpty : hsame (MatrixSingletonAddFold (xs ++ ys)) BHist.Empty :=
      Iff.mpr MatrixSingletonAddFold_append_carrier_iff
        (And.intro carrierData.right.left carrierData.right.right)
    have foldCarrier :
        MatrixSingletonAddFoldSpineCarrier (xs ++ ys) :=
      Iff.mp MatrixSingletonAddFold_carrier_iff foldEmpty
    exact Iff.mpr (MatrixSingletonAddFold_continuation_result_iff continuation)
      (And.intro carrierData.left foldCarrier)

theorem MatrixSingletonAddFold_continuation_empty_result_spine_iff {xs : List BHist}
    {y r : BHist} :
    Cont (MatrixSingletonAddFold xs) y r ->
      (hsame r BHist.Empty ↔ MatrixSingletonAddFoldSpineCarrier xs ∧ hsame y BHist.Empty) := by
  intro continuation
  constructor
  · intro resultEmpty
    have continuationEmpty :
        Cont (MatrixSingletonAddFold xs) y BHist.Empty :=
      cont_result_hsame_transport continuation resultEmpty
    have parts := cont_empty_result_inversion continuationEmpty
    exact And.intro (Iff.mp MatrixSingletonAddFold_carrier_iff parts.left) parts.right
  · intro data
    have foldEmpty : hsame (MatrixSingletonAddFold xs) BHist.Empty :=
      Iff.mpr MatrixSingletonAddFold_carrier_iff data.left
    exact cont_respects_hsame foldEmpty data.right continuation (cont_right_unit BHist.Empty)

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

theorem MatrixSingletonAddFold_zero_prefix_absorption {xs ys : List BHist} :
    MatrixSingletonAddFoldSpineCarrier xs ->
      MatrixSingletonAddFoldSpineCarrier ys ->
        MatrixSingletonClassifier (MatrixSingletonAddFold (xs ++ ys))
          (MatrixSingletonAddFold ys) := by
  intro xsCarrier ysCarrier
  have combinedCarrier : MatrixSingletonCarrier (MatrixSingletonAddFold (xs ++ ys)) :=
    Iff.mpr MatrixSingletonAddFold_append_carrier_iff (And.intro xsCarrier ysCarrier)
  have suffixCarrier : MatrixSingletonCarrier (MatrixSingletonAddFold ys) :=
    Iff.mpr MatrixSingletonAddFold_carrier_iff ysCarrier
  have displayedSame :
      hsame (MatrixSingletonAddFold (xs ++ ys))
        (append (MatrixSingletonAddFold xs) (MatrixSingletonAddFold ys)) :=
    MatrixSingletonAddFold_append_hsame
  have prefixEmpty : hsame (MatrixSingletonAddFold xs) BHist.Empty :=
    Iff.mpr MatrixSingletonAddFold_carrier_iff xsCarrier
  have displayedSuffixSame :
      hsame (append (MatrixSingletonAddFold xs) (MatrixSingletonAddFold ys))
        (MatrixSingletonAddFold ys) := by
    exact Eq.trans
      (congrArg (fun h : BHist => append h (MatrixSingletonAddFold ys)) prefixEmpty)
      (append_empty_left (MatrixSingletonAddFold ys))
  exact And.intro combinedCarrier
    (And.intro suffixCarrier (hsame_trans displayedSame displayedSuffixSame))

theorem MatrixSingletonAddFold_respects_classifier {xs ys : List BHist} :
    BEDC.Derived.ListUp.ListClassifierSpec MatrixSingletonClassifier xs ys ->
      MatrixSingletonAddFoldSpineCarrier xs ->
        MatrixSingletonAddFoldSpineCarrier ys ∧
          MatrixSingletonClassifier (append (MatrixSingletonAddFold xs) BHist.Empty)
            (append (MatrixSingletonAddFold ys) BHist.Empty) := by
  intro classified
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          intro _spine
          have emptySpine : MatrixSingletonAddFoldSpineCarrier ([] : List BHist) := by
            constructor
          have leftCarrier :
              MatrixSingletonCarrier (append (MatrixSingletonAddFold []) BHist.Empty) :=
            append_eq_empty_iff.mpr (And.intro (hsame_refl BHist.Empty)
              (hsame_refl BHist.Empty))
          exact And.intro emptySpine
            (And.intro leftCarrier (And.intro leftCarrier (hsame_refl _)))
      | cons y ys =>
          cases classified
  | cons x xs ih =>
      cases ys with
      | nil =>
          cases classified
      | cons y ys =>
          intro spine
          have tailData :=
            ih classified.right spine.right
          have targetSpine : MatrixSingletonAddFoldSpineCarrier (y :: ys) :=
            And.intro classified.left.right.left tailData.left
          have leftFoldCarrier :
              MatrixSingletonCarrier (MatrixSingletonAddFold (x :: xs)) :=
            Iff.mpr MatrixSingletonAddFold_carrier_iff spine
          have rightFoldCarrier :
              MatrixSingletonCarrier (MatrixSingletonAddFold (y :: ys)) :=
            Iff.mpr MatrixSingletonAddFold_carrier_iff targetSpine
          have leftDisplayCarrier :
              MatrixSingletonCarrier
                (append (MatrixSingletonAddFold (x :: xs)) BHist.Empty) :=
            append_eq_empty_iff.mpr
              (And.intro leftFoldCarrier (hsame_refl BHist.Empty))
          have rightDisplayCarrier :
              MatrixSingletonCarrier
                (append (MatrixSingletonAddFold (y :: ys)) BHist.Empty) :=
            append_eq_empty_iff.mpr
              (And.intro rightFoldCarrier (hsame_refl BHist.Empty))
          have displaySame :
              hsame (append (MatrixSingletonAddFold (x :: xs)) BHist.Empty)
                (append (MatrixSingletonAddFold (y :: ys)) BHist.Empty) :=
            hsame_trans leftDisplayCarrier (hsame_symm rightDisplayCarrier)
          exact And.intro targetSpine
            (And.intro leftDisplayCarrier (And.intro rightDisplayCarrier displaySame))

end BEDC.Derived.MatrixUp
