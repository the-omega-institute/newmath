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

theorem IntCarrier_continuation_closed_same_sign {sign : BEDC.FKernel.Mark.BMark}
    {h k r : BEDC.FKernel.Hist.BHist} :
    IntCarrier sign h -> IntCarrier sign k -> BEDC.FKernel.Cont.Cont h k r ->
      IntCarrier sign r := by
  intro ih ik cont
  cases ih with
  | intro signCases hUnary =>
      cases ik with
      | intro _ kUnary =>
          constructor
          · exact signCases
          · exact BEDC.FKernel.Unary.unary_cont_closed hUnary kUnary cont

theorem IntCarrier_transport_hsame_magnitude {sign : BEDC.FKernel.Mark.BMark}
    {h k : BEDC.FKernel.Hist.BHist} :
    IntCarrier sign h -> BEDC.FKernel.Hist.hsame h k -> IntCarrier sign k := by
  intro carrier sameMagnitude
  cases carrier with
  | intro signCases magnitudeUnary =>
      constructor
      · exact signCases
      · exact BEDC.FKernel.Unary.unary_transport magnitudeUnary sameMagnitude

end BEDC.Derived.IntUp
