import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_real_completion_root_window [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert realRoot :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont routes provenance realRoot ->
        PkgSig bundle realRoot pkg ->
          UnaryHistory domain ∧ UnaryHistory base ∧ UnaryHistory codomain ∧
            UnaryHistory magnitude ∧ UnaryHistory gradient ∧ UnaryHistory routes ∧
              UnaryHistory provenance ∧ UnaryHistory realRoot ∧ Cont domain base codomain ∧
                Cont codomain magnitude gradient ∧ Cont gradient transports routes ∧
                  Cont routes provenance realRoot ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle realRoot pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier routesProvenanceRoot realRootPkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, routesUnary, provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have realRootUnary : UnaryHistory realRoot :=
    unary_cont_closed routesUnary provenanceUnary routesProvenanceRoot
  exact
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary, routesUnary,
      provenanceUnary, realRootUnary, domainBaseCodomain, codomainMagnitudeGradient,
      gradientTransportsRoutes, routesProvenanceRoot, provenancePkg, realRootPkg⟩

end BEDC.Derived.SobolevUp
