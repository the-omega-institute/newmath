import BEDC.Derived.RegularCauchyTailScheduleUp.TasteGate

namespace BEDC.Derived.RegularCauchyTailScheduleUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegularCauchyTailSchedule_tail_meet_fusion_compatibility
    {Q R W D K T M F E H C P N route tailRead meetRead fusionRead : BHist} :
    UnaryHistory Q ->
      UnaryHistory R ->
        UnaryHistory W ->
          UnaryHistory M ->
            UnaryHistory F ->
              Cont Q R route ->
                Cont route W tailRead ->
                  Cont tailRead M meetRead ->
                    Cont tailRead F fusionRead ->
                      hsame M F ->
                        hsame meetRead fusionRead ∧
                          regularCauchyTailScheduleFromEventFlow
                              (regularCauchyTailScheduleToEventFlow
                                (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N)) =
                            some
                              (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory hsame RegularCauchyTailScheduleUp
  intro unaryQ unaryR unaryW unaryM unaryF routeQR routeTail routeMeet routeFusion sameConsumer
  have unaryRoute : UnaryHistory route := unary_cont_closed unaryQ unaryR routeQR
  have unaryTailRead : UnaryHistory tailRead :=
    unary_cont_closed unaryRoute unaryW routeTail
  have _unaryMeetRead : UnaryHistory meetRead :=
    unary_cont_closed unaryTailRead unaryM routeMeet
  have _unaryFusionRead : UnaryHistory fusionRead :=
    unary_cont_closed unaryTailRead unaryF routeFusion
  constructor
  · exact cont_respects_hsame (hsame_refl tailRead) sameConsumer routeMeet routeFusion
  · exact
      RegularCauchyTailScheduleTasteGate_single_carrier_alignment.2.1
        (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N)

end BEDC.Derived.RegularCauchyTailScheduleUp
