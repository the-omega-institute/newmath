namespace BEDC.Derived.ListUp

def ListCarrier (A : Type) := List A

def ListClassifierSpec {A : Type} (sameA : A → A → Prop) :
    ListCarrier A → ListCarrier A → Prop
  | [], [] => True
  | x :: xs, y :: ys => sameA x y ∧ ListClassifierSpec sameA xs ys
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

end BEDC.Derived.ListUp
