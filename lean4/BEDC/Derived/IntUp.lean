import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Unary.Commutativity

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

theorem IntCarrier_magnitude_induction {sign : BEDC.FKernel.Mark.BMark}
    {P : BEDC.FKernel.Hist.BHist -> Prop} :
    P BEDC.FKernel.Hist.BHist.Empty ->
      (forall h : BEDC.FKernel.Hist.BHist, IntCarrier sign h -> P h ->
        P (BEDC.FKernel.Hist.BHist.e1 h)) ->
      forall h : BEDC.FKernel.Hist.BHist, IntCarrier sign h -> P h := by
  intro base step h carrier
  cases carrier with
  | intro signCases magnitudeUnary =>
      exact BEDC.FKernel.Unary.unary_history_induction
        base
        (fun h unaryH ih => step h (And.intro signCases unaryH) ih)
        h
        magnitudeUnary

theorem IntCarrier_sign_msame_transport {sign sign' : BEDC.FKernel.Mark.BMark}
    {magnitude : BEDC.FKernel.Hist.BHist} :
    IntCarrier sign magnitude -> BEDC.FKernel.Mark.msame sign sign' ->
      IntCarrier sign' magnitude := by
  intro carrier sameSign
  cases sameSign
  exact carrier

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

theorem IntClassifierSpec_msame_sign_transport
    {sx sy sx' sy' : BEDC.FKernel.Mark.BMark} {hx hy : BEDC.FKernel.Hist.BHist} :
    IntClassifierSpec (sx, hx) (sy, hy) ->
      BEDC.FKernel.Mark.msame sx sx' ->
        BEDC.FKernel.Mark.msame sy sy' ->
          IntClassifierSpec (sx', hx) (sy', hy) := by
  intro classifier sameSx sameSy
  cases classifier with
  | intro carrierX rest =>
      cases rest with
      | intro carrierY sameRest =>
          cases sameRest with
          | intro sameSign sameMagnitude =>
              constructor
              · exact IntCarrier_sign_msame_transport carrierX sameSx
              · constructor
                · exact IntCarrier_sign_msame_transport carrierY sameSy
                · constructor
                  · exact BEDC.FKernel.Mark.msame_trans
                      (BEDC.FKernel.Mark.msame_trans
                        (BEDC.FKernel.Mark.msame_symm sameSx) sameSign)
                      sameSy
                  · exact sameMagnitude

theorem IntClassifierSpec_sign_magnitude_transport
    {sx sy sx' sy' : BEDC.FKernel.Mark.BMark}
    {hx hy hx' hy' : BEDC.FKernel.Hist.BHist} :
    IntClassifierSpec (sx, hx) (sy, hy) ->
      BEDC.FKernel.Mark.msame sx sx' ->
        BEDC.FKernel.Mark.msame sy sy' ->
          BEDC.FKernel.Hist.hsame hx hx' ->
            BEDC.FKernel.Hist.hsame hy hy' ->
              IntClassifierSpec (sx', hx') (sy', hy') := by
  intro classifier sameSx sameSy sameHx sameHy
  exact IntClassifierSpec_msame_sign_transport
    (IntClassifierSpec_hsame_magnitude_transport classifier sameHx sameHy)
    sameSx
    sameSy

theorem IntClassifierSpec_endpoint_sign_cases
    {x y : BEDC.FKernel.Mark.BMark × BEDC.FKernel.Hist.BHist} :
    IntClassifierSpec x y ->
      (((x.1 = BEDC.FKernel.Mark.BMark.b0 ∧ y.1 = BEDC.FKernel.Mark.BMark.b0) ∨
          (x.1 = BEDC.FKernel.Mark.BMark.b1 ∧ y.1 = BEDC.FKernel.Mark.BMark.b1)) ∧
        BEDC.FKernel.Unary.UnaryHistory x.2 ∧
          BEDC.FKernel.Unary.UnaryHistory y.2) := by
  intro classifier
  cases classifier with
  | intro carrierX rest =>
      cases rest with
      | intro carrierY sameRest =>
          cases sameRest with
          | intro sameSign _sameMagnitude =>
              cases IntCarrier_sign_cases carrierX with
              | inl zeroCase =>
                  exact And.intro
                    (Or.inl (And.intro zeroCase.left (sameSign.symm.trans zeroCase.left)))
                    (And.intro zeroCase.right carrierY.right)
              | inr oneCase =>
                  exact And.intro
                    (Or.inr (And.intro oneCase.left (sameSign.symm.trans oneCase.left)))
                    (And.intro oneCase.right carrierY.right)

theorem IntClassifierSpec_magnitude_pair_induction
    {P : BEDC.FKernel.Hist.BHist -> BEDC.FKernel.Hist.BHist -> Prop} :
    P BEDC.FKernel.Hist.BHist.Empty BEDC.FKernel.Hist.BHist.Empty ->
      (forall h k : BEDC.FKernel.Hist.BHist,
        BEDC.FKernel.Unary.UnaryHistory h -> BEDC.FKernel.Unary.UnaryHistory k ->
          P h k -> P (BEDC.FKernel.Hist.BHist.e1 h) k) ->
      (forall h k : BEDC.FKernel.Hist.BHist,
        BEDC.FKernel.Unary.UnaryHistory h -> BEDC.FKernel.Unary.UnaryHistory k ->
          P h k -> P h (BEDC.FKernel.Hist.BHist.e1 k)) ->
      forall {x y : BEDC.FKernel.Mark.BMark × BEDC.FKernel.Hist.BHist},
        IntClassifierSpec x y -> P x.2 y.2 := by
  intro base leftStep rightStep x y classifier
  cases classifier with
  | intro carrierX rest =>
      cases rest with
      | intro carrierY _sameData =>
          cases carrierX with
          | intro _signCasesX unaryX =>
              cases carrierY with
              | intro _signCasesY unaryY =>
                  have emptyLeft :
                      forall k : BEDC.FKernel.Hist.BHist,
                        BEDC.FKernel.Unary.UnaryHistory k ->
                          P BEDC.FKernel.Hist.BHist.Empty k := by
                    intro k unaryK
                    exact BEDC.FKernel.Unary.unary_history_induction
                      base
                      (fun k unaryK ih =>
                        rightStep BEDC.FKernel.Hist.BHist.Empty k
                          BEDC.FKernel.Unary.unary_empty unaryK ih)
                      k
                      unaryK
                  exact BEDC.FKernel.Unary.unary_history_induction
                    (P := fun h =>
                      forall k : BEDC.FKernel.Hist.BHist,
                        BEDC.FKernel.Unary.UnaryHistory k -> P h k)
                    emptyLeft
                    (fun h unaryH ih => by
                      intro k unaryK
                      exact leftStep h k unaryH unaryK (ih k unaryK))
                    x.2
                    unaryX
                    y.2
                    unaryY

theorem IntClassifierSpec_append_comm_same_sign {sign : BEDC.FKernel.Mark.BMark}
    {h k : BEDC.FKernel.Hist.BHist} :
    IntCarrier sign h -> IntCarrier sign k ->
      IntClassifierSpec (sign, BEDC.FKernel.Cont.append h k)
        (sign, BEDC.FKernel.Cont.append k h) := by
  intro carrierH carrierK
  cases carrierH with
  | intro signCases hUnary =>
      cases carrierK with
      | intro _ kUnary =>
          constructor
          · constructor
            · exact signCases
            · exact BEDC.FKernel.Unary.unary_append_closed hUnary kUnary
          · constructor
            · constructor
              · exact signCases
              · exact BEDC.FKernel.Unary.unary_append_closed kUnary hUnary
            · constructor
              · exact BEDC.FKernel.Mark.msame_refl sign
              · exact BEDC.FKernel.Unary.unary_append_comm hUnary kUnary

theorem IntClassifierSpec_append_context_same_sign
    {s : BEDC.FKernel.Mark.BMark} {left right a b : BEDC.FKernel.Hist.BHist} :
    IntCarrier s left -> IntCarrier s right ->
      IntClassifierSpec (s, a) (s, b) ->
        IntClassifierSpec
          (s, BEDC.FKernel.Cont.append left (BEDC.FKernel.Cont.append a right))
          (s, BEDC.FKernel.Cont.append left (BEDC.FKernel.Cont.append b right)) := by
  intro leftCarrier rightCarrier classified
  cases leftCarrier with
  | intro signCases leftUnary =>
      cases rightCarrier with
      | intro _ rightUnary =>
          cases classified with
          | intro carrierA classifiedRest =>
              cases classifiedRest with
              | intro carrierB sameData =>
                  cases carrierA with
                  | intro _ unaryA =>
                      cases carrierB with
                      | intro _ unaryB =>
                          cases sameData with
                          | intro _ sameMagnitude =>
                              constructor
                              · constructor
                                · exact signCases
                                · exact BEDC.FKernel.Unary.unary_append_closed leftUnary
                                    (BEDC.FKernel.Unary.unary_append_closed unaryA rightUnary)
                              · constructor
                                · constructor
                                  · exact signCases
                                  · exact BEDC.FKernel.Unary.unary_append_closed leftUnary
                                      (BEDC.FKernel.Unary.unary_append_closed unaryB rightUnary)
                                · constructor
                                  · exact BEDC.FKernel.Mark.msame_refl s
                                  · cases sameMagnitude
                                    exact BEDC.FKernel.Hist.hsame_refl
                                      (BEDC.FKernel.Cont.append left
                                        (BEDC.FKernel.Cont.append a right))

theorem IntClassifierSpec_cancel_append_context_same_sign
    {s : BEDC.FKernel.Mark.BMark} {left right a b : BEDC.FKernel.Hist.BHist} :
    IntCarrier s a -> IntCarrier s b ->
      IntClassifierSpec
        (s, BEDC.FKernel.Cont.append left (BEDC.FKernel.Cont.append a right))
        (s, BEDC.FKernel.Cont.append left (BEDC.FKernel.Cont.append b right)) ->
          IntClassifierSpec (s, a) (s, b) := by
  intro carrierA carrierB contextual
  cases contextual with
  | intro _ contextualRest =>
      cases contextualRest with
      | intro _ sameData =>
          cases sameData with
          | intro _ sameContext =>
              have sameTail :
                  BEDC.FKernel.Hist.hsame (BEDC.FKernel.Cont.append a right)
                    (BEDC.FKernel.Cont.append b right) := by
                exact BEDC.FKernel.Cont.append_left_cancel (h := left) sameContext
              have sameMagnitude : BEDC.FKernel.Hist.hsame a b := by
                exact BEDC.FKernel.Cont.append_right_cancel (k := right) sameTail
              constructor
              · exact carrierA
              · constructor
                · exact carrierB
                · constructor
                  · exact BEDC.FKernel.Mark.msame_refl s
                  · exact sameMagnitude

end BEDC.Derived.IntUp
