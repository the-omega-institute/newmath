import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BoolUp

open BEDC.FKernel.NameCert

local instance : NameCertSetup := MinimalNameCertSetup

abbrev BoolCarrier : Type := BEDC.FKernel.Mark.BMark

def BoolClassifierSpec : BoolCarrier → BoolCarrier → Prop :=
  BEDC.FKernel.Mark.msame

def BoolName : DerivedName := ()

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

theorem concrete_bool_namecert : BEDC.FKernel.NameCert.NameCert BoolName := by
  exact BEDC.FKernel.NameCert.NameCert.mk () () () () ()

end BEDC.Derived.BoolUp
