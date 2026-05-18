import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_present_route_package [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance name endpoint
      currentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        name endpoint bundle pkg ->
      Cont state route currentRead ->
        PkgSig bundle currentRead pkg ->
          UnaryHistory currentRead ∧ Cont observer route endpoint ∧
            Cont state route currentRead ∧ Cont recognition ledger gap ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle currentRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier stateRouteCurrent currentPkg
  obtain ⟨_observerUnary, stateUnary, _recognitionUnary, _ledgerUnary, _gapUnary,
    _transportUnary, routeUnary, _provenanceUnary, _nameUnary, _endpointUnary,
    observerRouteEndpoint, _stateRouteEndpoint, recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have currentUnary : UnaryHistory currentRead :=
    unary_cont_closed stateUnary routeUnary stateRouteCurrent
  exact
    ⟨currentUnary, observerRouteEndpoint, stateRouteCurrent, recognitionLedgerGap, endpointPkg,
      currentPkg⟩

end BEDC.Derived.ConsciousObserverStateUp
