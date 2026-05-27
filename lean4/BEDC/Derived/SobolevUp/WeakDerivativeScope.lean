import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_weak_derivative_scope [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert derivativeRead
      scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont domain gradient derivativeRead ->
        Cont derivativeRead localCert scopeRead ->
          PkgSig bundle scopeRead pkg ->
            UnaryHistory domain ∧ UnaryHistory gradient ∧ UnaryHistory localCert ∧
              UnaryHistory derivativeRead ∧ UnaryHistory scopeRead ∧
                Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
                  Cont domain gradient derivativeRead ∧
                    Cont derivativeRead localCert scopeRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle scopeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier derivativeRoute scopeRoute scopePkg
  obtain ⟨domainUnary, _baseUnary, _codomainUnary, _magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed domainUnary gradientUnary derivativeRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed derivativeUnary localCertUnary scopeRoute
  exact
    ⟨domainUnary, gradientUnary, localCertUnary, derivativeUnary, scopeUnary,
      domainBaseCodomain, codomainMagnitudeGradient, derivativeRoute, scopeRoute,
      provenancePkg, scopePkg⟩

end BEDC.Derived.SobolevUp
