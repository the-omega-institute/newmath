import BEDC.Derived.RegularCauchyTailScheduleUp.TasteGate

namespace BEDC.Derived.RegularCauchyTailScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailSchedule_bridge_route [AskSetup] [PackageSetup]
    {Q R W D K T M F E H C P N qr rw wd dk kt tm mf fe sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q ->
      UnaryHistory R ->
        UnaryHistory W ->
          UnaryHistory D ->
            UnaryHistory K ->
              UnaryHistory T ->
                UnaryHistory M ->
                  UnaryHistory F ->
                    UnaryHistory E ->
                      Cont Q R qr ->
                        Cont qr W rw ->
                          Cont rw D wd ->
                            Cont wd K dk ->
                              Cont dk T kt ->
                                Cont kt M tm ->
                                  Cont tm F mf ->
                                    Cont mf E fe ->
                                      PkgSig bundle P pkg ->
                                        PkgSig bundle sealedRead pkg ->
                                          hsame kt (append dk T) ∧
                                            hsame fe (append mf E) ∧
                                              UnaryHistory qr ∧
                                                UnaryHistory rw ∧
                                                  UnaryHistory wd ∧
                                                    UnaryHistory dk ∧
                                                      UnaryHistory kt ∧
                                                        UnaryHistory tm ∧
                                                          UnaryHistory mf ∧
                                                            UnaryHistory fe ∧
                                                              regularCauchyTailScheduleFromEventFlow
                                                                  (regularCauchyTailScheduleToEventFlow
                                                                    (RegularCauchyTailScheduleUp.mk
                                                                      Q R W D K T M F E H C P N)) =
                                                                some
                                                                  (RegularCauchyTailScheduleUp.mk
                                                                    Q R W D K T M F E H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont PkgSig UnaryHistory hsame
  intro unaryQ unaryR unaryW unaryD unaryK unaryT unaryM unaryF unaryE
    routeQR routeRW routeWD routeDK routeKT routeTM routeMF routeFE _pkgP _pkgSealed
  have unaryQR : UnaryHistory qr :=
    unary_cont_closed unaryQ unaryR routeQR
  have unaryRW : UnaryHistory rw :=
    unary_cont_closed unaryQR unaryW routeRW
  have unaryWD : UnaryHistory wd :=
    unary_cont_closed unaryRW unaryD routeWD
  have unaryDK : UnaryHistory dk :=
    unary_cont_closed unaryWD unaryK routeDK
  have unaryKT : UnaryHistory kt :=
    unary_cont_closed unaryDK unaryT routeKT
  have unaryTM : UnaryHistory tm :=
    unary_cont_closed unaryKT unaryM routeTM
  have unaryMF : UnaryHistory mf :=
    unary_cont_closed unaryTM unaryF routeMF
  have unaryFE : UnaryHistory fe :=
    unary_cont_closed unaryMF unaryE routeFE
  exact
    ⟨routeKT, routeFE, unaryQR, unaryRW, unaryWD, unaryDK, unaryKT, unaryTM, unaryMF,
      unaryFE,
      RegularCauchyTailScheduleTasteGate_single_carrier_alignment.2.1
        (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N)⟩

end BEDC.Derived.RegularCauchyTailScheduleUp
