import BEDC.Derived.RegularCauchyTailScheduleUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyTailScheduleUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegularCauchyTailSchedule_cofinal_window_induction
    {Q R W D K T M F E H C P N route windowRead dyadicRead cofinalRead tailWitness :
      BHist} :
    UnaryHistory Q ->
      UnaryHistory R ->
        UnaryHistory W ->
          UnaryHistory D ->
            UnaryHistory K ->
              UnaryHistory T ->
                Cont Q R route ->
                  Cont route W windowRead ->
                    Cont windowRead D dyadicRead ->
                      Cont dyadicRead K cofinalRead ->
                        Cont cofinalRead T tailWitness ->
                          UnaryHistory route /\
                            UnaryHistory windowRead /\
                              UnaryHistory dyadicRead /\
                                UnaryHistory cofinalRead /\
                                  UnaryHistory tailWitness /\
                                    hsame tailWitness (append cofinalRead T) /\
                                      regularCauchyTailScheduleFromEventFlow
                                          (regularCauchyTailScheduleToEventFlow
                                            (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N)) =
                                        some
                                          (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory RegularCauchyTailScheduleUp
  intro qUnary rUnary wUnary dUnary kUnary tUnary qrRoute routeWindow windowDyadic
    dyadicCofinal cofinalTail
  have routeUnary : UnaryHistory route :=
    unary_cont_closed qUnary rUnary qrRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed routeUnary wUnary routeWindow
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dUnary windowDyadic
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed dyadicUnary kUnary dyadicCofinal
  have tailUnary : UnaryHistory tailWitness :=
    unary_cont_closed cofinalUnary tUnary cofinalTail
  exact
    ⟨routeUnary, windowUnary, dyadicUnary, cofinalUnary, tailUnary, cofinalTail,
      RegularCauchyTailScheduleTasteGate_single_carrier_alignment.right.left
        (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N)⟩

end BEDC.Derived.RegularCauchyTailScheduleUp
