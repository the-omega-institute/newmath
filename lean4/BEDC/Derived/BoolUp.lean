import BEDC.FKernel.Mark

namespace BEDC.Derived.BoolUp

abbrev BoolCarrier : Type := BEDC.FKernel.Mark.BMark

def BoolClassifierSpec : BoolCarrier → BoolCarrier → Prop :=
  BEDC.FKernel.Mark.msame

def BoolSourceSpec (value : BEDC.FKernel.Mark.BMark) : Prop :=
  BEDC.FKernel.Mark.msame value BEDC.FKernel.Mark.BMark.b0 ∨
    BEDC.FKernel.Mark.msame value BEDC.FKernel.Mark.BMark.b1

theorem BoolClassifierSpec_constructor_separation :
    BoolClassifierSpec BEDC.FKernel.Mark.BMark.b0 BEDC.FKernel.Mark.BMark.b1 → False := by
  exact BEDC.FKernel.Mark.not_msame_b0_b1

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

theorem boolClassifierSpec_stability :
    BoolClassifierSpec BEDC.FKernel.Mark.BMark.b0 BEDC.FKernel.Mark.BMark.b0 /\
      BoolClassifierSpec BEDC.FKernel.Mark.BMark.b1 BEDC.FKernel.Mark.BMark.b1 /\
        (BoolClassifierSpec BEDC.FKernel.Mark.BMark.b0 BEDC.FKernel.Mark.BMark.b1 ->
          False) /\
          (BoolClassifierSpec BEDC.FKernel.Mark.BMark.b1 BEDC.FKernel.Mark.BMark.b0 ->
            False) := by
  constructor
  · exact BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b0
  · constructor
    · exact BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b1
    · constructor
      · exact BEDC.FKernel.Mark.not_msame_b0_b1
      · exact BEDC.FKernel.Mark.not_msame_b1_b0

theorem bool_stability_certificate :
    BoolSourceSpec BEDC.FKernel.Mark.BMark.b0 /\
      BoolSourceSpec BEDC.FKernel.Mark.BMark.b1 /\
      (BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b0
          BEDC.FKernel.Mark.BMark.b1 -> False) /\
        (BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b1
          BEDC.FKernel.Mark.BMark.b0 -> False) := by
  constructor
  · exact Or.inl rfl
  · constructor
    · exact Or.inr rfl
    · exact BEDC.FKernel.Mark.mark_no_confusion

theorem BoolSourceSpec_respects_msame {v w : BEDC.FKernel.Mark.BMark} :
    BoolSourceSpec v -> BEDC.FKernel.Mark.msame v w -> BoolSourceSpec w := by
  intro hv hvw
  cases hv with
  | inl hv0 =>
      exact Or.inl
        (BEDC.FKernel.Mark.msame_trans (BEDC.FKernel.Mark.msame_symm hvw) hv0)
  | inr hv1 =>
      exact Or.inr
        (BEDC.FKernel.Mark.msame_trans (BEDC.FKernel.Mark.msame_symm hvw) hv1)

end BEDC.Derived.BoolUp
