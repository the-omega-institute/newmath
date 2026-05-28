import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_pde_consumer_admission [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      pdeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont routes localCert pdeRead ->
        PkgSig bundle pdeRead pkg ->
          UnaryHistory domain ∧ UnaryHistory base ∧ UnaryHistory codomain ∧
            UnaryHistory magnitude ∧ UnaryHistory gradient ∧ UnaryHistory transports ∧
              UnaryHistory routes ∧ UnaryHistory localCert ∧ UnaryHistory pdeRead ∧
                Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
                  Cont gradient transports routes ∧ Cont routes localCert pdeRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle pdeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier pdeRoute pdePkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    transportsUnary, routesUnary, _provenanceUnary, localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have pdeReadUnary : UnaryHistory pdeRead :=
    unary_cont_closed routesUnary localCertUnary pdeRoute
  exact
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary, transportsUnary,
      routesUnary, localCertUnary, pdeReadUnary, domainBaseCodomain, codomainMagnitudeGradient,
      gradientTransportsRoutes, pdeRoute, provenancePkg, pdePkg⟩

end BEDC.Derived.SobolevUp
