import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_bridge_route [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance name endpoint
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        name endpoint bundle pkg ->
      Cont endpoint route bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          UnaryHistory bridgeRead ∧ Cont observer route endpoint ∧
            Cont state route endpoint ∧ Cont endpoint route bridgeRead ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier endpointRouteBridge bridgePkg
  obtain ⟨_observerUnary, _stateUnary, _recognitionUnary, _ledgerUnary, _gapUnary,
    _transportUnary, routeUnary, _provenanceUnary, _nameUnary, endpointUnary,
    observerRouteEndpoint, stateRouteEndpoint, _recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed endpointUnary routeUnary endpointRouteBridge
  exact
    ⟨bridgeUnary, observerRouteEndpoint, stateRouteEndpoint, endpointRouteBridge,
      endpointPkg, bridgePkg⟩

end BEDC.Derived.ConsciousObserverStateUp
