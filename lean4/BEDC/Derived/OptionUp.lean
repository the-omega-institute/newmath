namespace BEDC.Derived.OptionUp

theorem OptionCarrier_cases {α : Type} (x : Option α) :
    x = Option.none ∨ ∃ a : α, x = Option.some a := by
  cases x with
  | none =>
      exact Or.inl rfl
  | some a =>
      exact Or.inr ⟨a, rfl⟩

def OptionClassifierSpec {A : Type} (sameA : A -> A -> Prop) :
    Option A -> Option A -> Prop
  | none, none => True
  | some a, some b => sameA a b
  | none, some _ => False
  | some _, none => False

theorem optionClassifierSpec_cases {A : Type} {sameA : A -> A -> Prop} {x y : Option A} :
    OptionClassifierSpec sameA x y ->
      (x = none /\ y = none) \/
        (exists a : A, exists b : A, x = some a /\ y = some b /\ sameA a b) := by
  intro h
  cases x with
  | none =>
      cases y with
      | none =>
          exact Or.inl ⟨rfl, rfl⟩
      | some b =>
          cases h
  | some a =>
      cases y with
      | none =>
          cases h
      | some b =>
          exact Or.inr ⟨a, b, rfl, rfl, h⟩

end BEDC.Derived.OptionUp
