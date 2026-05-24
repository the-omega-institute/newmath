import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_uniform_tail_extraction [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      cofinalRequest refinedWindows refinedDyadic refinedSeal reusableTail
      boundedConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      UnaryHistory cofinalRequest ->
        Cont windows cofinalRequest refinedWindows ->
          Cont refinedWindows dyadic refinedDyadic ->
            Cont refinedDyadic readback refinedSeal ->
              Cont refinedSeal routes reusableTail ->
                Cont reusableTail sealRow boundedConsumer ->
                  PkgSig bundle boundedConsumer pkg ->
                    UnaryHistory refinedWindows ∧ UnaryHistory refinedDyadic ∧
                      UnaryHistory refinedSeal ∧ UnaryHistory reusableTail ∧
                        UnaryHistory boundedConsumer ∧ Cont windows cofinalRequest refinedWindows ∧
                          Cont refinedWindows dyadic refinedDyadic ∧
                            Cont refinedDyadic readback refinedSeal ∧
                              Cont refinedSeal routes reusableTail ∧
                                Cont reusableTail sealRow boundedConsumer ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle boundedConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier cofinalUnary windowsCofinal refinedDyadicCont refinedSealCont
  intro reusableTailCont boundedConsumerCont boundedConsumerPkg
  obtain ⟨_modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary, _modulusWindowRoute,
      _dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have refinedWindowsUnary : UnaryHistory refinedWindows :=
    unary_cont_closed windowsUnary cofinalUnary windowsCofinal
  have refinedDyadicUnary : UnaryHistory refinedDyadic :=
    unary_cont_closed refinedWindowsUnary dyadicUnary refinedDyadicCont
  have refinedSealUnary : UnaryHistory refinedSeal :=
    unary_cont_closed refinedDyadicUnary readbackUnary refinedSealCont
  have reusableTailUnary : UnaryHistory reusableTail :=
    unary_cont_closed refinedSealUnary routesUnary reusableTailCont
  have boundedConsumerUnary : UnaryHistory boundedConsumer :=
    unary_cont_closed reusableTailUnary sealUnary boundedConsumerCont
  exact
    ⟨refinedWindowsUnary, refinedDyadicUnary, refinedSealUnary, reusableTailUnary,
      boundedConsumerUnary, windowsCofinal, refinedDyadicCont, refinedSealCont,
      reusableTailCont, boundedConsumerCont, provenancePkg, boundedConsumerPkg⟩

end BEDC.Derived.RealCauchyModulusUp
