import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert tightenedWindow
      tightenedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      Cont windows dyadic tightenedWindow ->
        Cont tightenedWindow readback tightenedSeal ->
          PkgSig bundle localCert pkg ->
            UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory tightenedWindow ∧
                UnaryHistory tightenedSeal ∧ Cont windows dyadic tightenedWindow ∧
                  Cont tightenedWindow readback tightenedSeal ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localCert pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier tightenedWindowRoute tightenedSealRoute localCertPkg
  rcases carrier with
    ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary,
      _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary,
      _modulusWindowRoute, _dyadicReadbackRoute, _sealRoute, provenancePkg,
      _localSemantic⟩
  have tightenedWindowUnary : UnaryHistory tightenedWindow :=
    unary_cont_closed windowsUnary dyadicUnary tightenedWindowRoute
  have tightenedSealUnary : UnaryHistory tightenedSeal :=
    unary_cont_closed tightenedWindowUnary readbackUnary tightenedSealRoute
  exact
    ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary,
      tightenedWindowUnary, tightenedSealUnary, tightenedWindowRoute, tightenedSealRoute,
      provenancePkg, localCertPkg⟩

end BEDC.Derived.RealCauchyModulusUp
