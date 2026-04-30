import BEDC.FKernel.Hist

namespace BEDC.Derived.ListUp

def ListCarrier (A : Type) := List A

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

end BEDC.Derived.ListUp
