namespace BEDC.Derived.OptionUp

def OptionCarrier (A : Type) := Option A

def OptionClassifierSpec {A : Type} (sourceSame : A → A → Prop) :
    OptionCarrier A → OptionCarrier A → Prop
  | none, none => True
  | some a, some b => sourceSame a b
  | none, some _ => False
  | some _, none => False

def OptionClassifier {α : Type} (sourceSame : α → α → Prop)
    (x y : OptionCarrier α) : Prop :=
  match x, y with
  | Option.none, Option.none => True
  | Option.some a, Option.some b => sourceSame a b
  | Option.none, Option.some _ => False
  | Option.some _, Option.none => False

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

theorem option_classifier_inversion {A : Type} {sourceSame : A → A → Prop}
    {x y : Option A} :
    OptionClassifierSpec sourceSame x y →
      (x = none ∧ y = none) ∨
        (∃ a : A, ∃ b : A, x = some a ∧ y = some b ∧ sourceSame a b) := by
  exact optionClassifierSpec_cases

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

theorem OptionClassifierSpec_none_some_absurd {A : Type} {rel : A → A → Prop} {a : A} :
    OptionClassifierSpec rel (Option.none : OptionCarrier A) (Option.some a) → False := by
  intro h
  exact h

theorem OptionClassifierSpec_trans {A : Type} {Rel : A → A → Prop}
    (rel_trans : ∀ {a b c : A}, Rel a b → Rel b c → Rel a c) :
    ∀ {x y z : Option A},
      OptionClassifierSpec Rel x y →
        OptionClassifierSpec Rel y z →
          OptionClassifierSpec Rel x z := by
  intro x y z hxy hyz
  cases x <;> cases y <;> cases z <;> simp [OptionClassifierSpec] at *
  exact rel_trans hxy hyz

theorem optionClassifier_some_iff {α : Type} {sourceSame : α → α → Prop} {a b : α} :
    OptionClassifier sourceSame (Option.some a) (Option.some b) ↔ sourceSame a b := by
  constructor <;> intro h <;> exact h

end BEDC.Derived.OptionUp
