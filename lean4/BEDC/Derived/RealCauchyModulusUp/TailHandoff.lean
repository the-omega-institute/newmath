import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_tail_handoff [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      strongerRequest strongerWindows strongerDyadic strongerSeal completionConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      UnaryHistory strongerRequest ->
        Cont windows strongerRequest strongerWindows ->
          Cont strongerWindows dyadic strongerDyadic ->
            Cont strongerDyadic readback strongerSeal ->
              Cont strongerSeal routes completionConsumer ->
                PkgSig bundle completionConsumer pkg ->
                  UnaryHistory strongerWindows ∧ UnaryHistory strongerDyadic ∧
                    UnaryHistory strongerSeal ∧ UnaryHistory completionConsumer ∧
                      Cont modulus windows dyadic ∧ Cont dyadic readback sealRow ∧
                        Cont windows strongerRequest strongerWindows ∧
                          Cont strongerWindows dyadic strongerDyadic ∧
                            Cont strongerDyadic readback strongerSeal ∧
                              Cont strongerSeal routes completionConsumer ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle completionConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier strongerUnary windowsStronger strongerDyadicCont strongerSealCont
    completionCont completionPkg
  obtain ⟨_modulusUnary, windowsUnary, dyadicUnary, readbackUnary, _sealUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary, modulusWindowRoute,
      dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have strongerWindowsUnary : UnaryHistory strongerWindows :=
    unary_cont_closed windowsUnary strongerUnary windowsStronger
  have strongerDyadicUnary : UnaryHistory strongerDyadic :=
    unary_cont_closed strongerWindowsUnary dyadicUnary strongerDyadicCont
  have strongerSealUnary : UnaryHistory strongerSeal :=
    unary_cont_closed strongerDyadicUnary readbackUnary strongerSealCont
  have completionUnary : UnaryHistory completionConsumer :=
    unary_cont_closed strongerSealUnary routesUnary completionCont
  exact
    ⟨strongerWindowsUnary, strongerDyadicUnary, strongerSealUnary, completionUnary,
      modulusWindowRoute, dyadicReadbackRoute, windowsStronger, strongerDyadicCont,
      strongerSealCont, completionCont, provenancePkg, completionPkg⟩

end BEDC.Derived.RealCauchyModulusUp
