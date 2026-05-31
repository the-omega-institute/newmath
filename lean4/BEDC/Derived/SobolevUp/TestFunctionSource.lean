import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_test_function_source [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      testRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont domain gradient testRead ->
        PkgSig bundle testRead pkg ->
          UnaryHistory domain ∧ UnaryHistory base ∧ UnaryHistory codomain ∧
            UnaryHistory magnitude ∧ UnaryHistory gradient ∧ UnaryHistory testRead ∧
              Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
                Cont domain gradient testRead ∧ Cont gradient transports routes ∧
                  Cont routes provenance localCert ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle testRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier testRoute testPkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have testUnary : UnaryHistory testRead :=
    unary_cont_closed domainUnary gradientUnary testRoute
  exact
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary, testUnary,
      domainBaseCodomain, codomainMagnitudeGradient, testRoute, gradientTransportsRoutes,
      routesProvenanceLocalCert, provenancePkg, testPkg⟩

end BEDC.Derived.SobolevUp
