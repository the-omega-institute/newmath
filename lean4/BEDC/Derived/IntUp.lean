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

theorem IntClassifierSpec_refl {sign : BEDC.FKernel.Mark.BMark}
    {h : BEDC.FKernel.Hist.BHist} :
    IntCarrier sign h -> IntClassifierSpec (sign, h) (sign, h) := by
  intro carrier
  constructor
  · exact carrier
  · constructor
    · exact carrier
    · constructor
      · exact BEDC.FKernel.Mark.msame_refl sign
      · exact BEDC.FKernel.Hist.hsame_refl h

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

theorem IntClassifierSpec_continuation_closed_same_sign
    {sx sy sx' sy' : BEDC.FKernel.Mark.BMark}
    {hx hy hx' hy' r r' : BEDC.FKernel.Hist.BHist} :
    IntClassifierSpec (sx, hx) (sx', hx') ->
      IntClassifierSpec (sy, hy) (sy', hy') ->
        BEDC.FKernel.Mark.msame sx sy ->
          BEDC.FKernel.Cont.Cont hx hy r ->
            BEDC.FKernel.Cont.Cont hx' hy' r' ->
              IntClassifierSpec (sx, r) (sx', r') := by
  intro first second sameSigns cont cont'
  cases first with
  | intro carrierX firstRest =>
      cases firstRest with
      | intro carrierX' firstSame =>
          cases firstSame with
          | intro sameXX' sameHX =>
              cases second with
              | intro carrierY secondRest =>
                  cases secondRest with
                  | intro carrierY' secondSame =>
                      cases secondSame with
                      | intro sameYY' sameHY =>
                          have carrierYAsSX : IntCarrier sx hy := by
                            cases sameSigns
                            exact carrierY
                          have sameSX'SY' : BEDC.FKernel.Mark.msame sx' sy' :=
                            BEDC.FKernel.Mark.msame_trans
                              (BEDC.FKernel.Mark.msame_symm sameXX')
                              (BEDC.FKernel.Mark.msame_trans sameSigns sameYY')
                          have carrierY'AsSX' : IntCarrier sx' hy' := by
                            cases sameSX'SY'
                            exact carrierY'
                          constructor
                          · exact IntCarrier_continuation_closed_same_sign
                              carrierX carrierYAsSX cont
                          · constructor
                            · exact IntCarrier_continuation_closed_same_sign
                                carrierX' carrierY'AsSX' cont'
                            · constructor
                              · exact sameXX'
                              · exact BEDC.FKernel.Cont.cont_respects_hsame
                                  sameHX sameHY cont cont'

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

theorem IntClassifierSpec_hsame_magnitude_transport
    {sx sy : BEDC.FKernel.Mark.BMark} {hx hy hx' hy' : BEDC.FKernel.Hist.BHist} :
    IntClassifierSpec (sx, hx) (sy, hy) ->
      BEDC.FKernel.Hist.hsame hx hx' ->
        BEDC.FKernel.Hist.hsame hy hy' ->
          IntClassifierSpec (sx, hx') (sy, hy') := by
  intro classifier sameHx sameHy
  cases classifier with
  | intro carrierX rest =>
      cases rest with
      | intro carrierY sameRest =>
          cases sameRest with
          | intro sameSign sameMagnitude =>
              constructor
              · exact IntCarrier_transport_hsame_magnitude carrierX sameHx
              · constructor
                · exact IntCarrier_transport_hsame_magnitude carrierY sameHy
                · constructor
                  · exact sameSign
                  · exact BEDC.FKernel.Hist.hsame_trans
                      (BEDC.FKernel.Hist.hsame_trans
                        (BEDC.FKernel.Hist.hsame_symm sameHx) sameMagnitude)
                      sameHy

end BEDC.Derived.IntUp
