import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_dependency_handoff [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance nameRow endpoint
      handoffRead dependencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route
        provenance nameRow endpoint bundle pkg →
      Cont route provenance handoffRead →
        Cont handoffRead nameRow dependencyRead →
          PkgSig bundle handoffRead pkg →
            PkgSig bundle dependencyRead pkg →
              UnaryHistory observer ∧ UnaryHistory state ∧ UnaryHistory recognition ∧
              UnaryHistory ledger ∧ UnaryHistory gap ∧ UnaryHistory handoffRead ∧
              UnaryHistory dependencyRead ∧ Cont observer route endpoint ∧
              Cont state route endpoint ∧ Cont recognition ledger gap ∧
              Cont route provenance handoffRead ∧ Cont handoffRead nameRow dependencyRead ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle handoffRead pkg ∧
              PkgSig bundle dependencyRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg hsame Cont
  intro carrier routeProvenanceHandoff handoffNameDependency handoffPkg dependencyPkg
  obtain ⟨observerUnary, stateUnary, recognitionUnary, ledgerUnary, gapUnary,
    _transportUnary, routeUnary, provenanceUnary, nameUnary, _endpointUnary,
    observerRouteEndpoint, stateRouteEndpoint, recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceHandoff
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed handoffUnary nameUnary handoffNameDependency
  exact
    ⟨observerUnary, stateUnary, recognitionUnary, ledgerUnary, gapUnary, handoffUnary,
      dependencyUnary, observerRouteEndpoint, stateRouteEndpoint, recognitionLedgerGap,
      routeProvenanceHandoff, handoffNameDependency, endpointPkg, handoffPkg, dependencyPkg⟩

end BEDC.Derived.ConsciousObserverStateUp
