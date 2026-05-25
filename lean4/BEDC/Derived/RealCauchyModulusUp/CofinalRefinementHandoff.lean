import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_cofinal_refinement_handoff [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      cofinalRequest refinedWindows refinedDyadic refinedSeal cofinalConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      UnaryHistory cofinalRequest ->
        Cont windows cofinalRequest refinedWindows ->
          Cont refinedWindows dyadic refinedDyadic ->
            Cont refinedDyadic readback refinedSeal ->
              Cont refinedSeal routes cofinalConsumer ->
                PkgSig bundle cofinalConsumer pkg ->
                  UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory refinedWindows ∧
                    UnaryHistory refinedDyadic ∧ UnaryHistory refinedSeal ∧
                      UnaryHistory cofinalConsumer ∧ Cont modulus windows dyadic ∧
                        Cont windows cofinalRequest refinedWindows ∧
                          Cont refinedWindows dyadic refinedDyadic ∧
                            Cont refinedDyadic readback refinedSeal ∧
                              Cont refinedSeal routes cofinalConsumer ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle cofinalConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier cofinalUnary windowsCofinal refinedDyadicCont refinedSealCont
  intro cofinalConsumerCont cofinalConsumerPkg
  obtain ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, _sealUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary, modulusWindowRoute,
      _dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have refinedWindowsUnary : UnaryHistory refinedWindows :=
    unary_cont_closed windowsUnary cofinalUnary windowsCofinal
  have refinedDyadicUnary : UnaryHistory refinedDyadic :=
    unary_cont_closed refinedWindowsUnary dyadicUnary refinedDyadicCont
  have refinedSealUnary : UnaryHistory refinedSeal :=
    unary_cont_closed refinedDyadicUnary readbackUnary refinedSealCont
  have cofinalConsumerUnary : UnaryHistory cofinalConsumer :=
    unary_cont_closed refinedSealUnary routesUnary cofinalConsumerCont
  exact
    ⟨modulusUnary, windowsUnary, refinedWindowsUnary, refinedDyadicUnary, refinedSealUnary,
      cofinalConsumerUnary, modulusWindowRoute, windowsCofinal, refinedDyadicCont,
      refinedSealCont, cofinalConsumerCont, provenancePkg, cofinalConsumerPkg⟩

theorem RealCauchyModulusCarrier_cofinal_window_extraction [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      earlierRequest refinedRequest earlierWindow refinedWindow refinedDyadic : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg →
      UnaryHistory earlierRequest →
        UnaryHistory refinedRequest →
          Cont modulus earlierRequest earlierWindow →
            Cont earlierWindow refinedRequest refinedWindow →
              Cont refinedWindow dyadic refinedDyadic →
                UnaryHistory earlierWindow ∧ UnaryHistory refinedWindow ∧
                  UnaryHistory refinedDyadic ∧ Cont modulus earlierRequest earlierWindow ∧
                    Cont earlierWindow refinedRequest refinedWindow ∧
                      Cont refinedWindow dyadic refinedDyadic ∧
                        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier earlierUnary refinedUnary earlierWindowCont refinedWindowCont refinedDyadicCont
  obtain ⟨modulusUnary, _windowsUnary, dyadicUnary, _readbackUnary, _sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, _modulusWindowRoute,
      _dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have earlierWindowUnary : UnaryHistory earlierWindow :=
    unary_cont_closed modulusUnary earlierUnary earlierWindowCont
  have refinedWindowUnary : UnaryHistory refinedWindow :=
    unary_cont_closed earlierWindowUnary refinedUnary refinedWindowCont
  have refinedDyadicUnary : UnaryHistory refinedDyadic :=
    unary_cont_closed refinedWindowUnary dyadicUnary refinedDyadicCont
  exact
    ⟨earlierWindowUnary, refinedWindowUnary, refinedDyadicUnary, earlierWindowCont,
      refinedWindowCont, refinedDyadicCont, provenancePkg⟩

end BEDC.Derived.RealCauchyModulusUp
