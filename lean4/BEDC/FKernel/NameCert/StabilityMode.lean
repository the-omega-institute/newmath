namespace BEDC.FKernel.NameCert

inductive StabilityMode where
  | closure
  | reuse
  | descent
  | composition
  | seal

theorem stabilityMode_no_confusion :
    (StabilityMode.closure = StabilityMode.reuse -> False) /\
      (StabilityMode.closure = StabilityMode.descent -> False) /\
        (StabilityMode.reuse = StabilityMode.seal -> False) := by
  constructor
  · intro h
    cases h
  · constructor
    · intro h
      cases h
    · intro h
      cases h

theorem stabilityMode_exhaustive (mode : StabilityMode) :
    Or (mode = StabilityMode.closure)
      (Or (mode = StabilityMode.reuse)
        (Or (mode = StabilityMode.descent)
          (Or (mode = StabilityMode.composition) (mode = StabilityMode.seal)))) := by
  cases mode with
  | closure =>
      exact Or.inl rfl
  | reuse =>
      exact Or.inr (Or.inl rfl)
  | descent =>
      exact Or.inr (Or.inr (Or.inl rfl))
  | composition =>
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | «seal» =>
      exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

end BEDC.FKernel.NameCert
