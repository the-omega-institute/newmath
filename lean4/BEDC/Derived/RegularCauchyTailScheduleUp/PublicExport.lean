import BEDC.Derived.RegularCauchyTailScheduleUp
import BEDC.Derived.RegularCauchyTailScheduleUp.PublicConsumerSurface

namespace BEDC.Derived.RegularCauchyTailScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailSchedule_public_export [AskSetup] [PackageSetup]
    {Q R W D K T M F E H C P N qr rw wd dk kt tm mf fe completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailScheduleCarrier Q R W D K T M F E H C P N bundle pkg ->
      RegularCauchyTailSchedule_handoff_route Q R W D K T M F E H C P N qr rw tm mf fe ->
        Cont Q R qr ->
          Cont qr W rw ->
            Cont rw D wd ->
              Cont wd K dk ->
                Cont dk T kt ->
                  Cont kt M tm ->
                    Cont tm F mf ->
                      Cont mf E fe ->
                        Cont fe H completionRead ->
                          PkgSig bundle completionRead pkg ->
                            UnaryHistory completionRead ∧ hsame kt (append dk T) ∧
                              hsame fe (append mf E) ∧
                                regularCauchyTailScheduleFromEventFlow
                                    (regularCauchyTailScheduleToEventFlow
                                      (RegularCauchyTailScheduleUp.mk
                                        Q R W D K T M F E H C P N)) =
                                  some
                                    (RegularCauchyTailScheduleUp.mk
                                      Q R W D K T M F E H C P N) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier _handoff routeQR routeRW routeWD routeDK routeKT routeTM routeMF
    routeFE completionRoute completionPkg
  obtain ⟨_cert, _qrUnary, _rwUnary, _wdUnary, _dkUnary, _ktUnary, _tmUnary,
    _mfUnary, _feUnary, completionUnary⟩ :=
    RegularCauchyTailSchedule_public_consumer_surface
      carrier routeQR routeRW routeWD routeDK routeKT routeTM routeMF routeFE
      completionRoute completionPkg
  exact
    ⟨completionUnary, routeKT, routeFE,
      RegularCauchyTailScheduleTasteGate_single_carrier_alignment.right.left
        (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N)⟩

end BEDC.Derived.RegularCauchyTailScheduleUp
