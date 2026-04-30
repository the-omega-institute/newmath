namespace BEDC.Derived.OptionUp

theorem OptionCarrier_cases {α : Type} (x : Option α) :
    x = Option.none ∨ ∃ a : α, x = Option.some a := by
  cases x with
  | none =>
      exact Or.inl rfl
  | some a =>
      exact Or.inr ⟨a, rfl⟩

end BEDC.Derived.OptionUp
