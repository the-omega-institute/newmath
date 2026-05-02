import BEDC.Derived.ListUp.Reverse

namespace BEDC.Derived.ListUp

theorem ListClassifierSpec_BHist_append_left_cancel_classified
    {sameA : BEDC.FKernel.Hist.BHist -> BEDC.FKernel.Hist.BHist -> Prop}
    {pref pref' xs ys : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec sameA pref pref' ->
      ListClassifierSpec sameA (pref ++ xs) (pref' ++ ys) ->
        ListClassifierSpec sameA xs ys := by
  intro prefixClass appendClass
  induction pref generalizing pref' with
  | nil =>
      cases pref' with
      | nil =>
          exact appendClass
      | cons _ _ =>
          cases prefixClass
  | cons _ pref ih =>
      cases pref' with
      | nil =>
          cases prefixClass
      | cons _ pref' =>
          exact ih prefixClass.right appendClass.right

theorem ListClassifierSpec_hsame_append_context_iff
    {pref pref' xs ys suffix suffix' : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec BEDC.FKernel.Hist.hsame pref pref' →
      ListClassifierSpec BEDC.FKernel.Hist.hsame suffix suffix' →
        (ListClassifierSpec BEDC.FKernel.Hist.hsame
          (pref ++ (xs ++ suffix)) (pref' ++ (ys ++ suffix')) ↔
            ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys) := by
  intro prefixClass suffixClass
  constructor
  · intro contextClass
    have coreWithSuffix :
        ListClassifierSpec BEDC.FKernel.Hist.hsame (xs ++ suffix) (ys ++ suffix') :=
      ListClassifierSpec_hsame_append_left_cancel_classified prefixClass contextClass
    exact ListClassifierSpec_append_right_cancel_with_hsame_suffix suffixClass coreWithSuffix
  · intro coreClass
    exact ListClassifierSpec_append_hsame prefixClass
      (ListClassifierSpec_append_hsame coreClass suffixClass)

theorem ListClassifierSpec_BHist_append {sameA : BEDC.FKernel.Hist.BHist -> BEDC.FKernel.Hist.BHist -> Prop}
    {xs ys zs ws : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec sameA xs ys ->
      ListClassifierSpec sameA zs ws ->
        ListClassifierSpec sameA (xs ++ zs) (ys ++ ws) := by
  intro hxy hzw
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          exact hzw
      | cons _ _ =>
          cases hxy
  | cons _ xs ih =>
      cases ys with
      | nil =>
          cases hxy
      | cons _ _ =>
          cases hxy with
          | intro hhead htail =>
              constructor
              · exact hhead
              · exact ih htail

theorem ListClassifierSpec_append_right_cancel_classified {A : Type} {sameA : A → A → Prop}
    {xs ys suffix suffix' : BEDC.Derived.ListUp.ListCarrier A} :
    BEDC.Derived.ListUp.ListClassifierSpec sameA suffix suffix' →
      BEDC.Derived.ListUp.ListClassifierSpec sameA (xs ++ suffix) (ys ++ suffix') →
        BEDC.Derived.ListUp.ListClassifierSpec sameA xs ys := by
  intro suffixClass appendClass
  have leftCancel :
      ∀ {pref pref' xs ys : BEDC.Derived.ListUp.ListCarrier A},
        BEDC.Derived.ListUp.ListClassifierSpec sameA pref pref' →
          BEDC.Derived.ListUp.ListClassifierSpec sameA (pref ++ xs) (pref' ++ ys) →
            BEDC.Derived.ListUp.ListClassifierSpec sameA xs ys := by
    intro pref
    induction pref with
    | nil =>
        intro pref' xs ys prefixClass appendClass
        cases pref' with
        | nil =>
            exact appendClass
        | cons _ _ =>
            cases prefixClass
    | cons _ pref ih =>
        intro pref' xs ys prefixClass appendClass
        cases pref' with
        | nil =>
            cases prefixClass
        | cons _ pref' =>
            exact ih prefixClass.right appendClass.right
  have appendAssocPure :
      ∀ {A : Type}, ∀ xs ys zs : List A, (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
    intro A xs
    induction xs with
    | nil =>
        intro ys zs
        rfl
    | cons x xs ih =>
        intro ys zs
        exact congrArg (List.cons x) (ih ys zs)
  have appendNilPure : ∀ {A : Type}, ∀ xs : List A, xs ++ [] = xs := by
    intro A xs
    induction xs with
    | nil =>
        rfl
    | cons x xs ih =>
        exact congrArg (List.cons x) ih
  have reverseAuxPure :
      ∀ {A : Type}, ∀ xs ys : List A,
        List.reverseAux xs ys = List.reverseAux xs [] ++ ys := by
    intro A xs
    induction xs with
    | nil =>
        intro ys
        rfl
    | cons x xs ih =>
        intro ys
        exact (ih (x :: ys)).trans
          ((appendAssocPure (List.reverseAux xs []) [x] ys).symm.trans
            (congrArg (fun tail => tail ++ ys) (ih [x]).symm))
  have reverseConsPure :
      ∀ {A : Type}, ∀ x : A, ∀ xs : List A,
        List.reverse (x :: xs) = List.reverse xs ++ [x] := by
    intro A x xs
    change List.reverseAux xs [x] = List.reverseAux xs [] ++ [x]
    exact reverseAuxPure xs [x]
  have reverseAppendPure :
      ∀ {A : Type}, ∀ xs ys : List A,
        (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
    intro A xs
    induction xs with
    | nil =>
        intro ys
        change List.reverse ys = List.reverse ys ++ []
        exact (appendNilPure (List.reverse ys)).symm
    | cons x xs ih =>
        intro ys
        exact (reverseConsPure x (xs ++ ys)).trans
          ((congrArg (fun tail => tail ++ [x]) (ih ys)).trans
            ((appendAssocPure (List.reverse ys) (List.reverse xs) [x]).trans
              (congrArg (fun tail => List.reverse ys ++ tail) (reverseConsPure x xs).symm)))
  have reversedSuffix :
      BEDC.Derived.ListUp.ListClassifierSpec sameA suffix.reverse suffix'.reverse :=
    (BEDC.Derived.ListUp.ListClassifierSpec_reverse_iff
      (xs := suffix) (ys := suffix')).mp suffixClass
  have reversedAppend :
      BEDC.Derived.ListUp.ListClassifierSpec sameA
        (suffix.reverse ++ xs.reverse) (suffix'.reverse ++ ys.reverse) := by
    have raw :
        BEDC.Derived.ListUp.ListClassifierSpec sameA
          (xs ++ suffix).reverse (ys ++ suffix').reverse :=
      (BEDC.Derived.ListUp.ListClassifierSpec_reverse_iff
        (xs := xs ++ suffix) (ys := ys ++ suffix')).mp appendClass
    have leftEq :
        BEDC.Derived.ListUp.ListClassifierSpec sameA
          (xs ++ suffix).reverse (ys ++ suffix').reverse =
        BEDC.Derived.ListUp.ListClassifierSpec sameA
          (suffix.reverse ++ xs.reverse) (ys ++ suffix').reverse :=
      congrArg
        (fun left =>
          BEDC.Derived.ListUp.ListClassifierSpec sameA left (ys ++ suffix').reverse)
        (reverseAppendPure xs suffix)
    have shiftedLeft :
        BEDC.Derived.ListUp.ListClassifierSpec sameA
          (suffix.reverse ++ xs.reverse) (ys ++ suffix').reverse :=
      Eq.mp leftEq raw
    have rightEq :
        BEDC.Derived.ListUp.ListClassifierSpec sameA
          (suffix.reverse ++ xs.reverse) (ys ++ suffix').reverse =
        BEDC.Derived.ListUp.ListClassifierSpec sameA
          (suffix.reverse ++ xs.reverse) (suffix'.reverse ++ ys.reverse) :=
      congrArg
        (fun right =>
          BEDC.Derived.ListUp.ListClassifierSpec sameA (suffix.reverse ++ xs.reverse) right)
        (reverseAppendPure ys suffix')
    exact Eq.mp rightEq shiftedLeft
  have reversedCore :
      BEDC.Derived.ListUp.ListClassifierSpec sameA xs.reverse ys.reverse :=
    leftCancel reversedSuffix reversedAppend
  exact (BEDC.Derived.ListUp.ListClassifierSpec_reverse_iff
    (xs := xs) (ys := ys)).mpr reversedCore

theorem ListClassifierSpec_BHist_append_context_iff
    {sameA : BEDC.FKernel.Hist.BHist -> BEDC.FKernel.Hist.BHist -> Prop}
    {pref pref' xs ys suffix suffix' : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec sameA pref pref' ->
      ListClassifierSpec sameA suffix suffix' ->
        (ListClassifierSpec sameA (pref ++ (xs ++ suffix)) (pref' ++ (ys ++ suffix')) <->
          ListClassifierSpec sameA xs ys) := by
  intro prefixClass suffixClass
  constructor
  · intro contextClass
    have coreWithSuffix :
        ListClassifierSpec sameA (xs ++ suffix) (ys ++ suffix') :=
      ListClassifierSpec_BHist_append_left_cancel_classified prefixClass contextClass
    exact ListClassifierSpec_append_right_cancel_classified suffixClass coreWithSuffix
  · intro coreClass
    exact ListClassifierSpec_BHist_append prefixClass
      (ListClassifierSpec_BHist_append coreClass suffixClass)

end BEDC.Derived.ListUp
