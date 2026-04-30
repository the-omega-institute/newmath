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

end BEDC.Derived.ListUp
