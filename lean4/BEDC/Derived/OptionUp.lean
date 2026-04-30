namespace BEDC.Derived.OptionUp

def OptionCarrier (A : Type) := Option A

def OptionClassifierSpec {A : Type} (sameA : A → A → Prop) :
    OptionCarrier A → OptionCarrier A → Prop
  | none, none => True
  | some a, some b => sameA a b
  | none, some _ => False
  | some _, none => False

theorem OptionCarrier_cases {α : Type} (x : Option α) :
    x = Option.none ∨ ∃ a : α, x = Option.some a := by
  cases x with
  | none =>
      exact Or.inl rfl
  | some a =>
      exact Or.inr ⟨a, rfl⟩

theorem optionClassifierSpec_cases {A : Type} {sameA : A → A → Prop} {x y : Option A} :
    OptionClassifierSpec sameA x y →
      (x = none ∧ y = none) ∨
        (∃ a : A, ∃ b : A, x = some a ∧ y = some b ∧ sameA a b) := by
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

def OptionClassifier {A : Type} (same : A → A → Prop) : Option A → Option A → Prop
  | none, none => True
  | some a, some b => same a b
  | _, _ => False

theorem option_stability_certificate_fields {A : Type} {sameA : A → A → Prop}
    (reflA : ∀ a, sameA a a)
    (transA : ∀ {a b c}, sameA a b → sameA b c → sameA a c) :
    (OptionClassifierSpec sameA none none) ∧
      (∀ a : A, OptionClassifierSpec sameA (some a) (some a)) ∧
      (∀ {x y z : OptionCarrier A},
        OptionClassifierSpec sameA x y →
          OptionClassifierSpec sameA y z →
            OptionClassifierSpec sameA x z) ∧
      (∀ a : A, OptionClassifierSpec sameA none (some a) → False) ∧
      (∀ a : A, OptionClassifierSpec sameA (some a) none → False) := by
  constructor
  · exact True.intro
  · constructor
    · intro a
      exact reflA a
    · constructor
      · intro x y z hxy hyz
        cases x with
        | none =>
            cases y with
            | none =>
                cases z with
                | none =>
                    exact True.intro
                | some _ =>
                    exact hyz
            | some _ =>
                cases hxy
        | some _ =>
            cases y with
            | none =>
                cases hxy
            | some _ =>
                cases z with
                | none =>
                    exact hyz
                | some _ =>
                    exact transA hxy hyz
      · constructor
        · intro a h
          exact h
        · intro a h
          exact h

end BEDC.Derived.OptionUp
