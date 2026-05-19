import BEDC.Derived.TailBudgetCoherenceUp

namespace BEDC.Derived.TailBudgetCoherenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailBudgetCoherenceUp_StdBridge [AskSetup] [PackageSetup]
    {meet observationBudget selectorBudget agreementSeal limitSeal window readback dyadic
      transport routes provenance localCert endpoint bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal limitSeal
        window readback dyadic transport routes provenance localCert endpoint bundle pkg ->
      Cont endpoint routes bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          UnaryHistory bridgeRead ∧ hsame endpoint (append provenance localCert) ∧
            Cont endpoint routes bridgeRead ∧ PkgSig bundle endpoint pkg ∧
              PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier endpointRoutesBridge bridgePkg
  obtain ⟨_meetUnary, _observationBudgetUnary, _selectorBudgetUnary, _agreementSealUnary,
    _limitSealUnary, _windowUnary, _readbackUnary, _dyadicUnary, _transportUnary,
    routesUnary, _provenanceUnary, _localCertUnary, endpointUnary, _meetObservationWindow,
    _meetSelectorDyadic, _windowDyadicReadback, _readbackAgreementLimit,
    _limitTransportRoutes, _routesProvenanceLocal, _provenanceLocalEndpoint,
    sameEndpoint, endpointPkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed endpointUnary routesUnary endpointRoutesBridge
  exact ⟨bridgeUnary, sameEndpoint, endpointRoutesBridge, endpointPkg, bridgePkg⟩

end BEDC.Derived.TailBudgetCoherenceUp
