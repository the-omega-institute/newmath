import BEDC.Derived.ListUp.AppendContext
import BEDC.Derived.ListUp.PublicAppendLength
import BEDC.Derived.ListUp.PublicReverse

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

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

theorem FramedListPublicReverse_append_output_classifier_unique {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k r hRev kRev s t : BHist} :
    FramedListPublicAppend A h k r ->
      (exists xs : ListCarrier BHist, FramedListSpineRep A h xs ∧
        FramedListSpineRep A hRev xs.reverse) ->
        (exists ys : ListCarrier BHist, FramedListSpineRep A k ys ∧
          FramedListSpineRep A kRev ys.reverse) ->
          FramedListPublicAppend A kRev hRev s ->
            (exists zs : ListCarrier BHist, FramedListSpineRep A r zs ∧
              FramedListSpineRep A t zs.reverse) ->
              FramedListBridgeClassifier A Rel s t := by
  intro appendHK reverseH reverseK appendRev reverseR
  cases appendHK with
  | intro xs appendRest =>
      cases appendRest with
      | intro ys appendReps =>
          cases appendReps with
          | intro repH appendTail =>
              cases appendTail with
              | intro repK repR =>
                  cases reverseH with
                  | intro xsRev reverseHReps =>
                      cases reverseK with
                      | intro ysRev reverseKReps =>
                          cases appendRev with
                          | intro ysDisplayed appendRevRest =>
                              cases appendRevRest with
                              | intro xsDisplayed appendRevReps =>
                                  cases appendRevReps with
                                  | intro repKRevDisplayed appendRevTail =>
                                      cases appendRevTail with
                                      | intro repHRevDisplayed repS =>
                                          cases reverseR with
                                          | intro zs reverseRReps =>
                                              have classX :
                                                  ListClassifierSpec Rel xs xsRev := by
                                                exact FramedListSpineRep_coherence compat repH
                                                  reverseHReps.left
                                              have classY :
                                                  ListClassifierSpec Rel ys ysRev := by
                                                exact FramedListSpineRep_coherence compat repK
                                                  reverseKReps.left
                                              have classXRev :
                                                  ListClassifierSpec Rel xs.reverse
                                                    xsRev.reverse :=
                                                (ListClassifierSpec_reverse_iff
                                                  (sameA := Rel)).mp classX
                                              have classYRev :
                                                  ListClassifierSpec Rel ys.reverse
                                                    ysRev.reverse :=
                                                (ListClassifierSpec_reverse_iff
                                                  (sameA := Rel)).mp classY
                                              have classDisplayedY :
                                                  ListClassifierSpec Rel ysDisplayed
                                                    ys.reverse := by
                                                exact ListClassifierSpec_trans_from_nameCert cert
                                                  (FramedListSpineRep_coherence compat
                                                    repKRevDisplayed reverseKReps.right)
                                                  (ListClassifierSpec_symm_from_nameCert cert
                                                    classYRev)
                                              have classDisplayedX :
                                                  ListClassifierSpec Rel xsDisplayed
                                                    xs.reverse := by
                                                exact ListClassifierSpec_trans_from_nameCert cert
                                                  (FramedListSpineRep_coherence compat
                                                    repHRevDisplayed reverseHReps.right)
                                                  (ListClassifierSpec_symm_from_nameCert cert
                                                    classXRev)
                                              have classDisplayed :
                                                  ListClassifierSpec Rel (ysDisplayed ++ xsDisplayed)
                                                    (ys.reverse ++ xs.reverse) :=
                                                ListClassifierSpec_BHist_append classDisplayedY
                                                  classDisplayedX
                                              have reverseAppendClass :
                                                  ListClassifierSpec Rel (ys.reverse ++ xs.reverse)
                                                    zs.reverse := by
                                                have appendClass :
                                                    ListClassifierSpec Rel (xs ++ ys) zs :=
                                                  FramedListSpineRep_coherence compat repR
                                                    reverseRReps.left
                                                have reversedAppendClass :
                                                    ListClassifierSpec Rel (xs ++ ys).reverse
                                                      zs.reverse :=
                                                  (ListClassifierSpec_reverse_iff
                                                    (sameA := Rel)).mp appendClass
                                                have reverseAppendPure :
                                                    ∀ {A : Type}, ∀ xs ys : List A,
                                                      (xs ++ ys).reverse =
                                                        ys.reverse ++ xs.reverse := by
                                                  intro A xs
                                                  induction xs with
                                                  | nil =>
                                                      intro ys
                                                      have appendNilPure :
                                                          ∀ xs : List A, xs ++ [] = xs := by
                                                        intro xs
                                                        induction xs with
                                                        | nil =>
                                                            rfl
                                                        | cons x xs ih =>
                                                            exact congrArg (List.cons x) ih
                                                      change List.reverse ys =
                                                        List.reverse ys ++ []
                                                      exact (appendNilPure (List.reverse ys)).symm
                                                  | cons x xs ih =>
                                                      intro ys
                                                      have appendAssocPure :
                                                          ∀ xs ys zs : List A,
                                                            (xs ++ ys) ++ zs =
                                                              xs ++ (ys ++ zs) := by
                                                        intro xs
                                                        induction xs with
                                                        | nil =>
                                                            intro ys zs
                                                            rfl
                                                        | cons x xs ih =>
                                                            intro ys zs
                                                            exact congrArg (List.cons x)
                                                              (ih ys zs)
                                                      have reverseAuxPure :
                                                          ∀ xs ys : List A,
                                                            List.reverseAux xs ys =
                                                              List.reverseAux xs [] ++ ys := by
                                                        intro xs
                                                        induction xs with
                                                        | nil =>
                                                            intro ys
                                                            rfl
                                                        | cons x xs ihAux =>
                                                            intro ys
                                                            exact (ihAux (x :: ys)).trans
                                                              ((appendAssocPure
                                                                  (List.reverseAux xs []) [x]
                                                                  ys).symm.trans
                                                                (congrArg
                                                                  (fun tail => tail ++ ys)
                                                                  (ihAux [x]).symm))
                                                      have reverseConsPure :
                                                          ∀ x : A, ∀ xs : List A,
                                                            List.reverse (x :: xs) =
                                                              List.reverse xs ++ [x] := by
                                                        intro x xs
                                                        change List.reverseAux xs [x] =
                                                          List.reverseAux xs [] ++ [x]
                                                        exact reverseAuxPure xs [x]
                                                      exact (reverseConsPure x (xs ++ ys)).trans
                                                        ((congrArg (fun tail => tail ++ [x])
                                                          (ih ys)).trans
                                                          ((appendAssocPure (List.reverse ys)
                                                            (List.reverse xs) [x]).trans
                                                            (congrArg
                                                              (fun tail =>
                                                                List.reverse ys ++ tail)
                                                              (reverseConsPure x xs).symm)))
                                                have leftEq :
                                                    ListClassifierSpec Rel (xs ++ ys).reverse
                                                      zs.reverse =
                                                    ListClassifierSpec Rel
                                                      (ys.reverse ++ xs.reverse) zs.reverse :=
                                                  congrArg
                                                    (fun left =>
                                                      ListClassifierSpec Rel left zs.reverse)
                                                    (reverseAppendPure xs ys)
                                                exact Eq.mp leftEq reversedAppendClass
                                              have classSReversedR :
                                                  ListClassifierSpec Rel (ysDisplayed ++ xsDisplayed)
                                                    zs.reverse :=
                                                ListClassifierSpec_trans_from_nameCert cert
                                                  classDisplayed reverseAppendClass
                                              have classST :
                                                  ListClassifierSpec Rel (ysDisplayed ++ xsDisplayed)
                                                    zs.reverse := classSReversedR
                                              exact
                                                (FramedListBridgeClassifier_displayed_spine_exactness
                                                  cert compat repS reverseRReps.right).mpr classST

end BEDC.Derived.ListUp
