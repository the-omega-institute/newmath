import BEDC.Derived.RegularCauchyTailScheduleUp.BridgeRoute

namespace BEDC.Derived.RegularCauchyTailScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailSchedule_consumer_factorization [AskSetup] [PackageSetup]
    {Q R W D K T M F E H C P N qr rw wd dk kt tm mf fe completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailScheduleCarrier Q R W D K T M F E H C P N bundle pkg ->
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
                          UnaryHistory qr ∧
                            UnaryHistory rw ∧
                              UnaryHistory wd ∧
                                UnaryHistory dk ∧
                                  UnaryHistory kt ∧
                                    UnaryHistory tm ∧
                                      UnaryHistory mf ∧
                                        UnaryHistory fe ∧
                                          UnaryHistory completionRead ∧
                                            hsame kt (append dk T) ∧
                                              hsame fe (append mf E) ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame UnaryHistory
  intro carrier routeQR routeRW routeWD routeDK routeKT routeTM routeMF routeFE
    completionRoute completionPkg
  obtain ⟨qUnary, rUnary, wUnary, dUnary, kUnary, tUnary, mUnary, fUnary, eUnary,
    hUnary, _cUnary, _pUnary, _nUnary, _carrierQR, _carrierTail, _carrierMeet,
    _carrierSeal, provenancePkg, _namePkg⟩ := carrier
  have qrUnary : UnaryHistory qr :=
    unary_cont_closed qUnary rUnary routeQR
  have rwUnary : UnaryHistory rw :=
    unary_cont_closed qrUnary wUnary routeRW
  have wdUnary : UnaryHistory wd :=
    unary_cont_closed rwUnary dUnary routeWD
  have dkUnary : UnaryHistory dk :=
    unary_cont_closed wdUnary kUnary routeDK
  have ktUnary : UnaryHistory kt :=
    unary_cont_closed dkUnary tUnary routeKT
  have tmUnary : UnaryHistory tm :=
    unary_cont_closed ktUnary mUnary routeTM
  have mfUnary : UnaryHistory mf :=
    unary_cont_closed tmUnary fUnary routeMF
  have feUnary : UnaryHistory fe :=
    unary_cont_closed mfUnary eUnary routeFE
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed feUnary hUnary completionRoute
  exact
    ⟨qrUnary, rwUnary, wdUnary, dkUnary, ktUnary, tmUnary, mfUnary, feUnary,
      completionUnary, routeKT, routeFE, provenancePkg, completionPkg⟩

end BEDC.Derived.RegularCauchyTailScheduleUp
