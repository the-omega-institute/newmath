import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_weak_derivative_root_unblock_package [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert rootRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont gradient provenance rootRead ->
        PkgSig bundle rootRead pkg ->
          UnaryHistory domain ∧ UnaryHistory base ∧ UnaryHistory codomain ∧
            UnaryHistory magnitude ∧ UnaryHistory gradient ∧ UnaryHistory provenance ∧
              UnaryHistory rootRead ∧ Cont domain base codomain ∧
                Cont codomain magnitude gradient ∧ Cont gradient transports routes ∧
                  Cont routes provenance localCert ∧ Cont gradient provenance rootRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier gradientProvenanceRoot rootPkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed gradientUnary provenanceUnary gradientProvenanceRoot
  exact
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary, provenanceUnary,
      rootUnary, domainBaseCodomain, codomainMagnitudeGradient, gradientTransportsRoutes,
      routesProvenanceLocalCert, gradientProvenanceRoot, provenancePkg, rootPkg⟩

end BEDC.Derived.SobolevUp
