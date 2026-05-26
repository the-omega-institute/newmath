import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_bounded_readback_coherence [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      boundedModulus boundedWindows boundedDyadic boundedReadback boundedSeal
      boundedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      hsame modulus boundedModulus ->
        hsame windows boundedWindows ->
          hsame dyadic boundedDyadic ->
            hsame readback boundedReadback ->
              hsame sealRow boundedSeal ->
                Cont boundedReadback boundedSeal boundedRoute ->
                  PkgSig bundle boundedRoute pkg ->
                    hsame boundedRoute (append boundedReadback boundedSeal) ∧
                      UnaryHistory boundedRoute ∧ Cont dyadic readback sealRow ∧
                        Cont boundedReadback boundedSeal boundedRoute ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle boundedRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory Cont PkgSig
  intro carrier _sameModulus _sameWindows _sameDyadic sameReadback sameSeal boundedRouteCont
    boundedRoutePkg
  obtain ⟨_modulusUnary, _windowsUnary, _dyadicUnary, readbackUnary, sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, _modulusWindowRoute,
      dyadicReadbackSeal, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have boundedReadbackUnary : UnaryHistory boundedReadback :=
    unary_transport readbackUnary sameReadback
  have boundedSealUnary : UnaryHistory boundedSeal :=
    unary_transport sealUnary sameSeal
  have boundedRouteUnary : UnaryHistory boundedRoute :=
    unary_cont_closed boundedReadbackUnary boundedSealUnary boundedRouteCont
  have boundedRouteReadback : hsame boundedRoute (append boundedReadback boundedSeal) :=
    boundedRouteCont
  exact
    ⟨boundedRouteReadback, boundedRouteUnary, dyadicReadbackSeal, boundedRouteCont,
      provenancePkg, boundedRoutePkg⟩

end BEDC.Derived.RealCauchyModulusUp
