import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_completion_norm_handoff [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      completionRead normRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont base codomain completionRead ->
        Cont codomain magnitude normRead ->
          UnaryHistory completionRead ∧ UnaryHistory normRead ∧ UnaryHistory base ∧
            UnaryHistory codomain ∧ UnaryHistory magnitude ∧
              Cont base codomain completionRead ∧ Cont codomain magnitude normRead ∧
                Cont codomain magnitude gradient ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier completionRoute normRoute
  rcases carrier with
    ⟨_domainUnary, baseUnary, codomainUnary, magnitudeUnary, _gradientUnary,
      _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, _domainBaseCodomain,
      codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
      provenancePkg⟩
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed baseUnary codomainUnary completionRoute
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed codomainUnary magnitudeUnary normRoute
  exact
    ⟨completionUnary, normUnary, baseUnary, codomainUnary, magnitudeUnary,
      completionRoute, normRoute, codomainMagnitudeGradient, provenancePkg⟩

end BEDC.Derived.SobolevUp
