import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

theorem ListClassifierSpec_reverse_hsame_inversion :
    ∀ {xs ys : ListCarrier BEDC.FKernel.Hist.BHist},
      ListClassifierSpec BEDC.FKernel.Hist.hsame xs.reverse ys.reverse ->
        ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys := by
  have reverseReversePure :
      ∀ {A : Type}, ∀ xs : List A, xs.reverse.reverse = xs := by
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
    intro A xs
    induction xs with
    | nil =>
        rfl
    | cons x xs ih =>
        exact (congrArg List.reverse (reverseConsPure x xs)).trans
          ((reverseAppendPure xs.reverse [x]).trans
            ((congrArg (fun tail => [x].reverse ++ tail) ih).trans rfl))
  intro xs ys reversed
  have revRev :
      ListClassifierSpec BEDC.FKernel.Hist.hsame xs.reverse.reverse ys.reverse.reverse :=
    ListClassifierSpec_reverse_hsame reversed
  have originalLeft :
      ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys.reverse.reverse := by
    have leftEq :
        ListClassifierSpec BEDC.FKernel.Hist.hsame xs.reverse.reverse ys.reverse.reverse =
        ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys.reverse.reverse :=
      congrArg
        (fun left => ListClassifierSpec BEDC.FKernel.Hist.hsame left ys.reverse.reverse)
        (reverseReversePure xs)
    exact Eq.mp leftEq revRev
  have original :
      ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys := by
    have rightEq :
        ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys.reverse.reverse =
        ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys :=
      congrArg
        (fun right => ListClassifierSpec BEDC.FKernel.Hist.hsame xs right)
        (reverseReversePure ys)
    exact Eq.mp rightEq originalLeft
  exact original

theorem ListClassifierSpec_reverse_iff {A : Type} {sameA : A → A → Prop}
    {xs ys : BEDC.Derived.ListUp.ListCarrier A} :
    BEDC.Derived.ListUp.ListClassifierSpec sameA xs ys ↔
      BEDC.Derived.ListUp.ListClassifierSpec sameA xs.reverse ys.reverse := by
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
  have reverseReversePure :
      ∀ {A : Type}, ∀ xs : List A, xs.reverse.reverse = xs := by
    intro A xs
    induction xs with
    | nil =>
        rfl
    | cons x xs ih =>
        exact (congrArg List.reverse (reverseConsPure x xs)).trans
          ((reverseAppendPure xs.reverse [x]).trans
            ((congrArg (fun tail => [x].reverse ++ tail) ih).trans rfl))
  have reverseForward :
      ∀ {xs ys : BEDC.Derived.ListUp.ListCarrier A},
        BEDC.Derived.ListUp.ListClassifierSpec sameA xs ys →
          BEDC.Derived.ListUp.ListClassifierSpec sameA xs.reverse ys.reverse := by
    have aux :
        ∀ {xs ys accX accY : BEDC.Derived.ListUp.ListCarrier A},
          BEDC.Derived.ListUp.ListClassifierSpec sameA xs ys →
            BEDC.Derived.ListUp.ListClassifierSpec sameA accX accY →
              BEDC.Derived.ListUp.ListClassifierSpec sameA
                (List.reverseAux xs accX) (List.reverseAux ys accY) := by
      intro xs
      induction xs with
      | nil =>
          intro ys accX accY hxy hacc
          cases ys with
          | nil =>
              exact hacc
          | cons _ _ =>
              cases hxy
      | cons x xs ih =>
          intro ys accX accY hxy hacc
          cases ys with
          | nil =>
              cases hxy
          | cons y ys =>
              cases hxy with
              | intro hhead htail =>
                  exact ih (ys := ys) (accX := x :: accX) (accY := y :: accY)
                    htail (And.intro hhead hacc)
    intro xs ys hxy
    change BEDC.Derived.ListUp.ListClassifierSpec sameA
      (List.reverseAux xs []) (List.reverseAux ys [])
    exact aux hxy (by constructor)
  constructor
  · intro classifier
    exact reverseForward classifier
  · intro reversed
    have revRev :
        BEDC.Derived.ListUp.ListClassifierSpec sameA xs.reverse.reverse ys.reverse.reverse :=
      reverseForward reversed
    have originalLeft :
        BEDC.Derived.ListUp.ListClassifierSpec sameA xs ys.reverse.reverse := by
      have leftEq :
          BEDC.Derived.ListUp.ListClassifierSpec sameA xs.reverse.reverse ys.reverse.reverse =
          BEDC.Derived.ListUp.ListClassifierSpec sameA xs ys.reverse.reverse :=
        congrArg
          (fun left =>
            BEDC.Derived.ListUp.ListClassifierSpec sameA left ys.reverse.reverse)
          (reverseReversePure xs)
      exact Eq.mp leftEq revRev
    have original :
        BEDC.Derived.ListUp.ListClassifierSpec sameA xs ys := by
      have rightEq :
          BEDC.Derived.ListUp.ListClassifierSpec sameA xs ys.reverse.reverse =
          BEDC.Derived.ListUp.ListClassifierSpec sameA xs ys :=
        congrArg
          (fun right => BEDC.Derived.ListUp.ListClassifierSpec sameA xs right)
          (reverseReversePure ys)
      exact Eq.mp rightEq originalLeft
    exact original

end BEDC.Derived.ListUp
