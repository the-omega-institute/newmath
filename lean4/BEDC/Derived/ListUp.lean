import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ListUp

abbrev ListCarrier (A : Type) := List A

def ListClassifierSpec {A : Type} (sameA : A → A → Prop) :
    ListCarrier A → ListCarrier A → Prop
  | [], [] => True
  | x :: xs, y :: ys => sameA x y ∧ ListClassifierSpec sameA xs ys
  | [], _ :: _ => False
  | _ :: _, [] => False

def ListClassifier {α : Type} (sourceSame : α → α → Prop) :
    List α → List α → Prop
  | [], [] => True
  | x :: xs, y :: ys => sourceSame x y ∧ ListClassifier sourceSame xs ys
  | [], _ :: _ => False
  | _ :: _, [] => False

theorem list_stability_reflexive_by_induction {A : Type} {sameA : A → A → Prop}
    (reflA : ∀ a, sameA a a) : ∀ xs : ListCarrier A, ListClassifierSpec sameA xs xs := by
  intro xs
  induction xs with
  | nil =>
      exact True.intro
  | cons x xs ih =>
      constructor
      · exact reflA x
      · exact ih

theorem listClassifier_refl {α : Type} {sourceSame : α → α → Prop}
    (sourceRefl : ∀ a : α, sourceSame a a) : ∀ xs : List α, ListClassifier sourceSame xs xs := by
  intro xs
  induction xs with
  | nil =>
      constructor
  | cons x xs ih =>
      constructor
      · exact sourceRefl x
      · exact ih

theorem ListClassifierSpec_trans {A : Type} {rel : A → A → Prop}
    (rel_trans : ∀ {a b c : A}, rel a b → rel b c → rel a c) :
    ∀ {xs ys zs : BEDC.Derived.ListUp.ListCarrier A},
      BEDC.Derived.ListUp.ListClassifierSpec rel xs ys →
        BEDC.Derived.ListUp.ListClassifierSpec rel ys zs →
          BEDC.Derived.ListUp.ListClassifierSpec rel xs zs := by
  intro xs
  induction xs with
  | nil =>
      intro ys zs hxy hyz
      cases ys with
      | nil =>
          cases zs with
          | nil =>
              change BEDC.Derived.ListUp.ListClassifierSpec rel [] []
              constructor
          | cons z zs =>
              cases hyz
      | cons y ys =>
          cases hxy
  | cons x xs ih =>
      intro ys zs hxy hyz
      cases ys with
      | nil =>
          cases hxy
      | cons y ys =>
          cases zs with
          | nil =>
              cases hyz
          | cons z zs =>
              cases hxy with
              | intro hxyHead hxyTail =>
                  cases hyz with
                  | intro hyzHead hyzTail =>
                      constructor
                      · exact rel_trans hxyHead hyzHead
                      · exact ih hxyTail hyzTail

theorem ListClassifierSpec_hsame_trans :
    forall {xs ys zs : ListCarrier BEDC.FKernel.Hist.BHist},
      ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys ->
        ListClassifierSpec BEDC.FKernel.Hist.hsame ys zs ->
          ListClassifierSpec BEDC.FKernel.Hist.hsame xs zs := by
  intro xs
  induction xs with
  | nil =>
      intro ys zs hxy hyz
      cases ys with
      | nil =>
          cases zs with
          | nil =>
              constructor
          | cons z zs =>
              cases hyz
      | cons y ys =>
          cases hxy
  | cons x xs ih =>
      intro ys zs hxy hyz
      cases ys with
      | nil =>
          cases hxy
      | cons y ys =>
          cases zs with
          | nil =>
              cases hyz
          | cons z zs =>
              cases hxy with
              | intro hxyHead hxyTail =>
                  cases hyz with
                  | intro hyzHead hyzTail =>
                      constructor
                      · exact BEDC.FKernel.Hist.hsame_trans hxyHead hyzHead
                      · exact ih hxyTail hyzTail

theorem ListClassifierSpec_trans_from_nameCert
    {Carrier : BEDC.FKernel.Hist.BHist -> Prop}
    {sameA : BEDC.FKernel.Hist.BHist -> BEDC.FKernel.Hist.BHist -> Prop}
    (cert : BEDC.FKernel.NameCert.NameCert Carrier sameA) :
    forall {xs ys zs : List BEDC.FKernel.Hist.BHist},
      ListClassifierSpec sameA xs ys ->
        ListClassifierSpec sameA ys zs ->
          ListClassifierSpec sameA xs zs := by
  intro xs
  induction xs with
  | nil =>
      intro ys zs sameXY sameYZ
      cases ys with
      | nil =>
          cases zs with
          | nil =>
              constructor
          | cons z zs =>
              cases sameYZ
      | cons y ys =>
          cases sameXY
  | cons x xs ih =>
      intro ys zs sameXY sameYZ
      cases ys with
      | nil =>
          cases sameXY
      | cons y ys =>
          cases zs with
          | nil =>
              cases sameYZ
          | cons z zs =>
              cases sameXY with
              | intro sameXYHead sameXYTail =>
                  cases sameYZ with
                  | intro sameYZHead sameYZTail =>
                      constructor
                      · exact cert.equiv_trans sameXYHead sameYZHead
                      · exact ih sameXYTail sameYZTail

theorem ListClassifierSpec_hsame_symm :
    forall {xs ys : ListCarrier BEDC.FKernel.Hist.BHist},
      ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys ->
        ListClassifierSpec BEDC.FKernel.Hist.hsame ys xs := by
  intro xs
  induction xs with
  | nil =>
      intro ys hxy
      cases ys with
      | nil =>
          constructor
      | cons _ _ =>
          cases hxy
  | cons _ xs ih =>
      intro ys hxy
      cases ys with
      | nil =>
          cases hxy
      | cons _ _ =>
          cases hxy with
          | intro hhead htail =>
              constructor
              · exact BEDC.FKernel.Hist.hsame_symm hhead
              · exact ih htail

theorem ListClassifierSpec_hsame_map_e0 :
    forall {xs ys : ListCarrier BEDC.FKernel.Hist.BHist},
      ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys ->
        ListClassifierSpec BEDC.FKernel.Hist.hsame
          (xs.map BEDC.FKernel.Hist.BHist.e0) (ys.map BEDC.FKernel.Hist.BHist.e0) := by
  intro xs
  induction xs with
  | nil =>
      intro ys hxy
      cases ys with
      | nil =>
          constructor
      | cons _ _ =>
          cases hxy
  | cons x xs ih =>
      intro ys hxy
      cases ys with
      | nil =>
          cases hxy
      | cons y ys =>
          cases hxy with
          | intro hhead htail =>
              constructor
              · exact BEDC.FKernel.Hist.hsame_e0_congr hhead
              · exact ih htail

theorem ListClassifierSpec_hsame_map_e0_inversion :
    forall {xs ys : ListCarrier BEDC.FKernel.Hist.BHist},
      ListClassifierSpec BEDC.FKernel.Hist.hsame
        (xs.map BEDC.FKernel.Hist.BHist.e0) (ys.map BEDC.FKernel.Hist.BHist.e0) ->
        ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys mapped
      cases ys with
      | nil =>
          constructor
      | cons _ _ =>
          cases mapped
  | cons _ xs ih =>
      intro ys mapped
      cases ys with
      | nil =>
          cases mapped
      | cons _ ys =>
          cases mapped with
          | intro head tail =>
              constructor
              · exact BEDC.FKernel.Hist.hsame_e0_iff.mp head
              · exact ih tail

theorem ListClassifierSpec_hsame_map_e1 :
    forall {xs ys : ListCarrier BEDC.FKernel.Hist.BHist},
      ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys ->
        ListClassifierSpec BEDC.FKernel.Hist.hsame
          (xs.map BEDC.FKernel.Hist.BHist.e1) (ys.map BEDC.FKernel.Hist.BHist.e1) := by
  intro xs
  induction xs with
  | nil =>
      intro ys hxy
      cases ys with
      | nil =>
          constructor
      | cons _ _ =>
          cases hxy
  | cons x xs ih =>
      intro ys hxy
      cases ys with
      | nil =>
          cases hxy
      | cons y ys =>
          cases hxy with
          | intro hhead htail =>
              constructor
              · exact BEDC.FKernel.Hist.hsame_e1_congr hhead
              · exact ih htail

theorem ListClassifierSpec_hsame_length_eq :
    forall {xs ys : ListCarrier BEDC.FKernel.Hist.BHist},
      ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys ->
        xs.length = ys.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys same
      cases ys with
      | nil =>
          rfl
      | cons _ _ =>
          cases same
  | cons _ xs ih =>
      intro ys same
      cases ys with
      | nil =>
          cases same
      | cons _ ys =>
          cases same with
          | intro headSame tailSame =>
              cases headSame
              exact congrArg Nat.succ (ih tailSame)

theorem ListClassifierSpec_append_hsame
    {xs ys zs ws : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys ->
      ListClassifierSpec BEDC.FKernel.Hist.hsame zs ws ->
        ListClassifierSpec BEDC.FKernel.Hist.hsame (xs ++ zs) (ys ++ ws) := by
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

theorem ListClassifierSpec_append_left_cancel_hsame
    {pref xs ys : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec BEDC.FKernel.Hist.hsame (pref ++ xs) (pref ++ ys) ->
      ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys := by
  intro sameWithPrefix
  induction pref with
  | nil =>
      exact sameWithPrefix
  | cons _ pref ih =>
      cases sameWithPrefix with
      | intro _ sameTail =>
          exact ih sameTail

theorem ListClassifierSpec_hsame_append_left_cancel
    {«prefix» xs ys : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec BEDC.FKernel.Hist.hsame («prefix» ++ xs) («prefix» ++ ys) ->
      ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys := by
  intro same
  induction «prefix» with
  | nil =>
      exact same
  | cons _ «prefix» ih =>
      cases same with
      | intro _ sameTail =>
          exact ih sameTail

theorem ListClassifierSpec_reverse_hsame :
    ∀ {xs ys : BEDC.Derived.ListUp.ListCarrier BEDC.FKernel.Hist.BHist},
      ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys →
        ListClassifierSpec BEDC.FKernel.Hist.hsame xs.reverse ys.reverse := by
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
  have reverseAuxPure :
      ∀ {A : Type}, ∀ xs ys : List A, List.reverseAux xs ys = List.reverseAux xs [] ++ ys := by
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
      ∀ {A : Type}, ∀ x : A, ∀ xs : List A, List.reverse (x :: xs) = List.reverse xs ++ [x] := by
    intro A x xs
    change List.reverseAux xs [x] = List.reverseAux xs [] ++ [x]
    exact reverseAuxPure xs [x]
  have aux :
      ∀ {xs ys accX accY : BEDC.Derived.ListUp.ListCarrier BEDC.FKernel.Hist.BHist},
        ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys →
          ListClassifierSpec BEDC.FKernel.Hist.hsame accX accY →
            ListClassifierSpec BEDC.FKernel.Hist.hsame
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
  change ListClassifierSpec BEDC.FKernel.Hist.hsame
    (List.reverseAux xs []) (List.reverseAux ys [])
  exact aux hxy (by constructor)

end BEDC.Derived.ListUp
