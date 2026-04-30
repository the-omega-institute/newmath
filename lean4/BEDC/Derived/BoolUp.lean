import BEDC.FKernel.Mark

namespace BEDC.Derived.BoolUp

def BoolCarrier : Type := BEDC.FKernel.Mark.BMark

def BoolSourceSpec (value : BEDC.FKernel.Mark.BMark) : Prop :=
  BEDC.FKernel.Mark.msame value BEDC.FKernel.Mark.BMark.b0 ∨
    BEDC.FKernel.Mark.msame value BEDC.FKernel.Mark.BMark.b1

theorem bool_stability_certificate_fields :
    (BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b0 BEDC.FKernel.Mark.BMark.b0 ∧
        BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b1 BEDC.FKernel.Mark.BMark.b1) ∧
      (BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b0 BEDC.FKernel.Mark.BMark.b1 →
        False) ∧
      (BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b1 BEDC.FKernel.Mark.BMark.b0 →
        False) ∧
      (∀ v : BEDC.FKernel.Mark.BMark, BoolSourceSpec v) := by
  constructor
  · constructor
    · rfl
    · rfl
  · constructor
    · intro h
      cases h
    · constructor
      · intro h
        cases h
      · intro v
        cases v with
        | b0 =>
            exact Or.inl rfl
        | b1 =>
            exact Or.inr rfl

end BEDC.Derived.BoolUp
