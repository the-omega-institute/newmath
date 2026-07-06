import BEDC.Derived.RegularCauchyTailScheduleUp.ConsumerFactorization

namespace BEDC.Derived.RegularCauchyTailScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyTailSchedule_handoff_route
    (Q R W D K T M F E H C P N route tailRead meetRead fusionRead sealRead : BHist) :
    Prop :=
  -- BEDC touchpoint anchor: BHist Cont
  Cont Q R route ∧ Cont route W tailRead ∧ Cont tailRead M meetRead ∧
    Cont meetRead F fusionRead ∧ Cont fusionRead E sealRead

theorem RegularCauchyTailSchedule_carrier_route_rows [AskSetup] [PackageSetup]
    {Q R W D K T M F E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailScheduleCarrier Q R W D K T M F E H C P N bundle pkg →
      UnaryHistory Q ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory D ∧
        UnaryHistory K ∧ UnaryHistory T ∧ UnaryHistory M ∧ UnaryHistory F ∧
          UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
            UnaryHistory N ∧ Cont Q R C ∧ Cont C W T ∧ Cont T M F ∧
              Cont F E H ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier
  rcases carrier with
    ⟨unaryQ, unaryR, unaryW, unaryD, unaryK, unaryT, unaryM, unaryF, unaryE,
      unaryH, unaryC, unaryP, unaryN, routeQR, routeCW, routeTM, routeFE,
      provenancePkg, namePkg⟩
  exact
    ⟨unaryQ, unaryR, unaryW, unaryD, unaryK, unaryT, unaryM, unaryF, unaryE,
      unaryH, unaryC, unaryP, unaryN, routeQR, routeCW, routeTM, routeFE,
      provenancePkg, namePkg⟩

theorem RegularCauchyTailSchedule_scoped_closure_certificate [AskSetup] [PackageSetup]
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
                          SemanticNameCert
                              (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row Q ∨ hsame row R ∨ hsame row W ∨ hsame row D ∨
                                  hsame row K ∨ hsame row T ∨ hsame row M ∨
                                    hsame row F ∨ hsame row E ∨ hsame row completionRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont Q R qr ∧ Cont qr W rw ∧
                                  Cont rw D wd ∧ Cont wd K dk ∧ Cont dk T kt ∧
                                    Cont kt M tm ∧ Cont tm F mf ∧ Cont mf E fe ∧
                                      Cont fe H completionRead ∧
                                        PkgSig bundle completionRead pkg)
                              hsame ∧
                            UnaryHistory qr ∧ UnaryHistory rw ∧ UnaryHistory wd ∧
                              UnaryHistory dk ∧ UnaryHistory kt ∧ UnaryHistory tm ∧
                                UnaryHistory mf ∧ UnaryHistory fe ∧
                                  UnaryHistory completionRead ∧ hsame kt (append dk T) ∧
                                    hsame fe (append mf E) ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert
  intro carrier routeQR routeRW routeWD routeDK routeKT routeTM routeMF routeFE
    completionRoute completionPkg
  obtain ⟨completionCert, qrUnaryScope, rwUnaryScope, wdUnaryScope, dkUnaryScope,
    ktUnaryScope, tmUnaryScope, mfUnaryScope, feUnaryScope, completionUnaryScope,
    ktReadbackScope, feReadbackScope⟩ :=
    RegularCauchyTailSchedule_real_completion_scope
      carrier routeQR routeRW routeWD routeDK routeKT routeTM routeMF routeFE
      completionRoute completionPkg
  obtain ⟨_qrUnaryConsumer, _rwUnaryConsumer, _wdUnaryConsumer, _dkUnaryConsumer,
    _ktUnaryConsumer, _tmUnaryConsumer, _mfUnaryConsumer, _feUnaryConsumer,
    _completionUnaryConsumer, _ktReadbackConsumer, _feReadbackConsumer,
    provenancePkg, completionPkgConsumer⟩ :=
    RegularCauchyTailSchedule_consumer_factorization
      carrier routeQR routeRW routeWD routeDK routeKT routeTM routeMF routeFE
      completionRoute completionPkg
  exact
    ⟨completionCert, qrUnaryScope, rwUnaryScope, wdUnaryScope, dkUnaryScope,
      ktUnaryScope, tmUnaryScope, mfUnaryScope, feUnaryScope, completionUnaryScope,
      ktReadbackScope, feReadbackScope, provenancePkg, completionPkgConsumer⟩

end BEDC.Derived.RegularCauchyTailScheduleUp
