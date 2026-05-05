import BEDC.Derived.ListUp.AppendContext

namespace BEDC.Derived.ListUp

theorem ListClassifierSpec_hsame_reverse_append_antimorphism
    {xs ys xsRev ysRev : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec BEDC.FKernel.Hist.hsame xsRev xs.reverse ->
      ListClassifierSpec BEDC.FKernel.Hist.hsame ysRev ys.reverse ->
        ListClassifierSpec BEDC.FKernel.Hist.hsame (List.reverse (xs ++ ys)) (ysRev ++ xsRev) := by
  intro xsClass ysClass
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
      ∀ {A : Type}, ∀ xs ys : List A, (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
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
  have core :
      ListClassifierSpec BEDC.FKernel.Hist.hsame (ys.reverse ++ xs.reverse)
        (ysRev ++ xsRev) := by
    exact ListClassifierSpec_append_hsame (ListClassifierSpec_hsame_symm ysClass)
      (ListClassifierSpec_hsame_symm xsClass)
  have leftEq :
      ListClassifierSpec BEDC.FKernel.Hist.hsame (ys.reverse ++ xs.reverse)
        (ysRev ++ xsRev) =
      ListClassifierSpec BEDC.FKernel.Hist.hsame (List.reverse (xs ++ ys)) (ysRev ++ xsRev) :=
    congrArg
      (fun left => ListClassifierSpec BEDC.FKernel.Hist.hsame left (ysRev ++ xsRev))
      (reverseAppendPure xs ys).symm
  exact Eq.mp leftEq core

theorem ListClassifierSpec_hsame_map_e1_reverse_append_antimorphism
    {xs ys xsRev ysRev : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec BEDC.FKernel.Hist.hsame xsRev xs.reverse ->
      ListClassifierSpec BEDC.FKernel.Hist.hsame ysRev ys.reverse ->
        ListClassifierSpec BEDC.FKernel.Hist.hsame
          ((xs ++ ys).reverse.map BEDC.FKernel.Hist.BHist.e1)
          ((ysRev ++ xsRev).map BEDC.FKernel.Hist.BHist.e1) := by
  intro xsClass ysClass
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
      ∀ {A : Type}, ∀ xs ys : List A, (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
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
  have core :
      ListClassifierSpec BEDC.FKernel.Hist.hsame (ys.reverse ++ xs.reverse)
        (ysRev ++ xsRev) := by
    exact ListClassifierSpec_append_hsame (ListClassifierSpec_hsame_symm ysClass)
      (ListClassifierSpec_hsame_symm xsClass)
  have reversedCore :
      ListClassifierSpec BEDC.FKernel.Hist.hsame (xs ++ ys).reverse (ysRev ++ xsRev) := by
    have leftEq :
        ListClassifierSpec BEDC.FKernel.Hist.hsame (ys.reverse ++ xs.reverse)
          (ysRev ++ xsRev) =
        ListClassifierSpec BEDC.FKernel.Hist.hsame (xs ++ ys).reverse (ysRev ++ xsRev) :=
      congrArg
        (fun left => ListClassifierSpec BEDC.FKernel.Hist.hsame left (ysRev ++ xsRev))
        (reverseAppendPure xs ys).symm
    exact Eq.mp leftEq core
  exact ListClassifierSpec_hsame_map_e1 reversedCore

theorem ListClassifierSpec_hsame_map_e0_reverse_append_antimorphism
    {xs ys xsRev ysRev : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec BEDC.FKernel.Hist.hsame xsRev xs.reverse ->
      ListClassifierSpec BEDC.FKernel.Hist.hsame ysRev ys.reverse ->
        ListClassifierSpec BEDC.FKernel.Hist.hsame
          ((xs ++ ys).reverse.map BEDC.FKernel.Hist.BHist.e0)
          ((ysRev ++ xsRev).map BEDC.FKernel.Hist.BHist.e0) := by
  intro xsClass ysClass
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
      ∀ {A : Type}, ∀ xs ys : List A, (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
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
  have core :
      ListClassifierSpec BEDC.FKernel.Hist.hsame (ys.reverse ++ xs.reverse)
        (ysRev ++ xsRev) := by
    exact ListClassifierSpec_append_hsame (ListClassifierSpec_hsame_symm ysClass)
      (ListClassifierSpec_hsame_symm xsClass)
  have reversedCore :
      ListClassifierSpec BEDC.FKernel.Hist.hsame (xs ++ ys).reverse (ysRev ++ xsRev) := by
    have leftEq :
        ListClassifierSpec BEDC.FKernel.Hist.hsame (ys.reverse ++ xs.reverse)
          (ysRev ++ xsRev) =
        ListClassifierSpec BEDC.FKernel.Hist.hsame (xs ++ ys).reverse (ysRev ++ xsRev) :=
      congrArg
        (fun left => ListClassifierSpec BEDC.FKernel.Hist.hsame left (ysRev ++ xsRev))
        (reverseAppendPure xs ys).symm
    exact Eq.mp leftEq core
  exact ListClassifierSpec_hsame_map_e0 reversedCore

end BEDC.Derived.ListUp
