import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_weak_derivative_route [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      exists weakRoute : BHist,
        UnaryHistory weakRoute ∧
          hsame weakRoute (append (append (append (append domain base) codomain) magnitude)
            gradient) ∧
            Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
              Cont gradient transports routes ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro carrier
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have domainBaseUnary : UnaryHistory (append domain base) :=
    unary_append_closed domainUnary baseUnary
  have domainBaseCodomainUnary :
      UnaryHistory (append (append domain base) codomain) :=
    unary_append_closed domainBaseUnary codomainUnary
  have domainBaseCodomainMagnitudeUnary :
      UnaryHistory (append (append (append domain base) codomain) magnitude) :=
    unary_append_closed domainBaseCodomainUnary magnitudeUnary
  exact
    ⟨append (append (append (append domain base) codomain) magnitude) gradient,
      unary_append_closed domainBaseCodomainMagnitudeUnary gradientUnary, hsame_refl _,
      domainBaseCodomain, codomainMagnitudeGradient, gradientTransportsRoutes, provenancePkg⟩

end BEDC.Derived.SobolevUp
