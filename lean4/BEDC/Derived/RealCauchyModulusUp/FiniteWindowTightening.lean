import BEDC.Derived.RealCauchyModulusUp.UniformTailExtraction

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_finite_window_tightening [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      tightenedRequest tightenedWindows tightenedDyadic tightenedSeal tightenedTail
      boundedConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      UnaryHistory tightenedRequest ->
        Cont windows tightenedRequest tightenedWindows ->
          Cont tightenedWindows dyadic tightenedDyadic ->
            Cont tightenedDyadic readback tightenedSeal ->
              Cont tightenedSeal routes tightenedTail ->
                Cont tightenedTail sealRow boundedConsumer ->
                  PkgSig bundle boundedConsumer pkg ->
                    UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory tightenedWindows ∧
                      UnaryHistory tightenedDyadic ∧ UnaryHistory tightenedSeal ∧
                        UnaryHistory tightenedTail ∧ UnaryHistory boundedConsumer ∧
                          Cont modulus windows dyadic ∧
                            Cont windows tightenedRequest tightenedWindows ∧
                              Cont tightenedWindows dyadic tightenedDyadic ∧
                                Cont tightenedDyadic readback tightenedSeal ∧
                                  Cont tightenedSeal routes tightenedTail ∧
                                    Cont tightenedTail sealRow boundedConsumer ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle boundedConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier tightenedUnary windowsTightened tightenedDyadicCont tightenedSealCont
  intro tightenedTailCont boundedConsumerCont boundedConsumerPkg
  have carrierCore := carrier
  obtain ⟨modulusUnary, windowsUnary, _dyadicUnary, _readbackUnary, _sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, modulusWindowRoute,
      _dyadicReadbackRoute, _sealRoute, _provenancePkg, _localSemantic⟩ := carrier
  have tailExtraction :=
    RealCauchyModulusCarrier_uniform_tail_extraction
      (modulus := modulus) (windows := windows) (dyadic := dyadic) (readback := readback)
      (sealRow := sealRow) (transports := transports) (routes := routes)
      (provenance := provenance) (localCert := localCert)
      (cofinalRequest := tightenedRequest) (refinedWindows := tightenedWindows)
      (refinedDyadic := tightenedDyadic) (refinedSeal := tightenedSeal)
      (reusableTail := tightenedTail) (boundedConsumer := boundedConsumer)
      (bundle := bundle) (pkg := pkg) carrierCore tightenedUnary windowsTightened
      tightenedDyadicCont tightenedSealCont tightenedTailCont boundedConsumerCont
      boundedConsumerPkg
  obtain ⟨tightenedWindowsUnary, tightenedDyadicUnary, tightenedSealUnary,
    tightenedTailUnary, boundedConsumerUnary, _windowsTightened, _tightenedDyadicCont,
      _tightenedSealCont, _tightenedTailCont, _boundedConsumerCont, provenancePkg,
        boundedConsumerPkg'⟩ := tailExtraction
  exact
    ⟨modulusUnary, windowsUnary, tightenedWindowsUnary, tightenedDyadicUnary,
      tightenedSealUnary, tightenedTailUnary, boundedConsumerUnary, modulusWindowRoute,
      windowsTightened, tightenedDyadicCont, tightenedSealCont, tightenedTailCont,
      boundedConsumerCont, provenancePkg, boundedConsumerPkg'⟩

end BEDC.Derived.RealCauchyModulusUp
