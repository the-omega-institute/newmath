import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_trace_boundary_obligation [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont routes localCert boundaryRead ->
        PkgSig bundle boundaryRead pkg ->
          UnaryHistory domain ∧ UnaryHistory base ∧ UnaryHistory codomain ∧
            UnaryHistory magnitude ∧ UnaryHistory gradient ∧ UnaryHistory routes ∧
              UnaryHistory localCert ∧ UnaryHistory boundaryRead ∧ Cont domain base codomain ∧
                Cont codomain magnitude gradient ∧ Cont gradient transports routes ∧
                  Cont routes localCert boundaryRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier routesLocalBoundary boundaryPkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, routesUnary, _provenanceUnary, localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed routesUnary localCertUnary routesLocalBoundary
  exact
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary, routesUnary,
      localCertUnary, boundaryUnary, domainBaseCodomain, codomainMagnitudeGradient,
      gradientTransportsRoutes, routesLocalBoundary, provenancePkg, boundaryPkg⟩

end BEDC.Derived.SobolevUp
