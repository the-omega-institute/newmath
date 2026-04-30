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

theorem IntCarrier_magnitude_hsame_transport {sign : BEDC.FKernel.Mark.BMark}
    {h k : BEDC.FKernel.Hist.BHist} :
    IntCarrier sign h → BEDC.FKernel.Hist.hsame h k → IntCarrier sign k := by
  intro carrier same
  cases carrier with
  | intro signCases magnitude =>
      constructor
      · exact signCases
      · exact BEDC.FKernel.Unary.unary_transport magnitude same

def IntSourceSpec (sign : BEDC.FKernel.Mark.BMark) (magnitude : BEDC.FKernel.Hist.BHist) :
    Prop :=
  IntCarrier sign magnitude

def IntClassifierSpec
    (x y : BEDC.FKernel.Mark.BMark × BEDC.FKernel.Hist.BHist) : Prop :=
  BEDC.Derived.IntUp.IntCarrier x.1 x.2 ∧
    BEDC.Derived.IntUp.IntCarrier y.1 y.2 ∧
      BEDC.FKernel.Mark.msame x.1 y.1 ∧ BEDC.FKernel.Hist.hsame x.2 y.2

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

theorem IntClassifierSpec_trans
    {x y z : BEDC.FKernel.Mark.BMark × BEDC.FKernel.Hist.BHist} :
    IntClassifierSpec x y -> IntClassifierSpec y z -> IntClassifierSpec x z := by
  intro xy yz
  cases xy with
  | intro carrierX xyRest =>
      cases xyRest with
      | intro _ xySame =>
          cases xySame with
          | intro sameSignXY sameMagnitudeXY =>
              cases yz with
              | intro _ yzRest =>
                  cases yzRest with
                  | intro carrierZ yzSame =>
                      cases yzSame with
                      | intro sameSignYZ sameMagnitudeYZ =>
                          constructor
                          · exact carrierX
                          · constructor
                            · exact carrierZ
                            · constructor
                              · exact BEDC.FKernel.Mark.msame_trans sameSignXY sameSignYZ
                              · exact BEDC.FKernel.Hist.hsame_trans sameMagnitudeXY sameMagnitudeYZ

theorem IntClassifierSpec_symm
    {x y : BEDC.FKernel.Mark.BMark × BEDC.FKernel.Hist.BHist} :
    IntClassifierSpec x y -> IntClassifierSpec y x := by
  intro xy
  cases xy with
  | intro carrierX xyRest =>
      cases xyRest with
      | intro carrierY sameXY =>
          cases sameXY with
          | intro sameSign sameMagnitude =>
              constructor
              · exact carrierY
              · constructor
                · exact carrierX
                · constructor
                  · exact BEDC.FKernel.Mark.msame_symm sameSign
                  · exact BEDC.FKernel.Hist.hsame_symm sameMagnitude

end BEDC.Derived.IntUp
