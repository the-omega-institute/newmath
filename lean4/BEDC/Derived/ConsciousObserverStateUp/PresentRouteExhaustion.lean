import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_present_route_exhaustion [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance name endpoint
      presentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        name endpoint bundle pkg ->
      Cont ledger gap presentRead ->
        PkgSig bundle presentRead pkg ->
          UnaryHistory observer ∧ UnaryHistory state ∧ UnaryHistory recognition ∧
            UnaryHistory ledger ∧ UnaryHistory gap ∧ UnaryHistory transport ∧
              UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                UnaryHistory endpoint ∧ UnaryHistory presentRead ∧
                  Cont observer route endpoint ∧ Cont state route endpoint ∧
                    Cont recognition ledger gap ∧ Cont transport provenance endpoint ∧
                      Cont ledger gap presentRead ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle presentRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont
  intro carrier ledgerGapPresent presentPkg
  obtain ⟨observerUnary, stateUnary, recognitionUnary, ledgerUnary, gapUnary,
    transportUnary, routeUnary, provenanceUnary, nameUnary, endpointUnary,
    observerRouteEndpoint, stateRouteEndpoint, recognitionLedgerGap,
    transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have presentUnary : UnaryHistory presentRead :=
    unary_cont_closed ledgerUnary gapUnary ledgerGapPresent
  exact
    ⟨observerUnary, stateUnary, recognitionUnary, ledgerUnary, gapUnary, transportUnary,
      routeUnary, provenanceUnary, nameUnary, endpointUnary, presentUnary,
      observerRouteEndpoint, stateRouteEndpoint, recognitionLedgerGap,
      transportProvenanceEndpoint, ledgerGapPresent, endpointPkg, presentPkg⟩

end BEDC.Derived.ConsciousObserverStateUp
