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

end BEDC.FKernel.NameCert
