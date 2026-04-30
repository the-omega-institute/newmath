import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.IntUp

def IntCarrier
    (sign : BEDC.FKernel.Mark.BMark) (magnitude : BEDC.FKernel.Hist.BHist) : Prop :=
  (sign = BEDC.FKernel.Mark.BMark.b0 ∨ sign = BEDC.FKernel.Mark.BMark.b1) ∧
    BEDC.FKernel.Unary.UnaryHistory magnitude

theorem IntCarrier_sign_cases {sign : BEDC.FKernel.Mark.BMark}
    {magnitude : BEDC.FKernel.Hist.BHist} :
    IntCarrier sign magnitude →
      (sign = BEDC.FKernel.Mark.BMark.b0 ∧
        BEDC.FKernel.Unary.UnaryHistory magnitude) ∨
        (sign = BEDC.FKernel.Mark.BMark.b1 ∧
          BEDC.FKernel.Unary.UnaryHistory magnitude) := by
  intro h
  cases h with
  | intro hsign hmagnitude =>
      cases hsign with
      | inl hzero =>
          exact Or.inl ⟨hzero, hmagnitude⟩
      | inr hone =>
          exact Or.inr ⟨hone, hmagnitude⟩

def IntSourceSpec (sign : BEDC.FKernel.Mark.BMark) (magnitude : BEDC.FKernel.Hist.BHist) :
    Prop :=
  IntCarrier sign magnitude

theorem intup_source_specification
    (sign : BEDC.FKernel.Mark.BMark) (magnitude : BEDC.FKernel.Hist.BHist) :
    IntSourceSpec sign magnitude <-> IntCarrier sign magnitude := by
  rfl

end BEDC.Derived.IntUp
