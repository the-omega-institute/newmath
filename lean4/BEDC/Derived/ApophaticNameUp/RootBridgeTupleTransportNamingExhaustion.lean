import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_bridge_tuple_transport_naming_exhaustion
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow structuralRead endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont transport route structuralRead ->
        Cont structuralRead nameRow endpoint ->
          PkgSig bundle endpoint pkg ->
            UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
              UnaryHistory nameRow ∧ UnaryHistory structuralRead ∧ UnaryHistory endpoint ∧
                Cont transport route structuralRead ∧ Cont structuralRead nameRow endpoint ∧
                  Cont gate ledger nameRow ∧ hsame ledger (append request gate) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier transportRouteStructural structuralNameEndpoint endpointPkg
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, _ledgerUnary, transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed transportUnary routeUnary transportRouteStructural
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed structuralUnary nameRowUnary structuralNameEndpoint
  exact
    ⟨transportUnary, routeUnary, provenanceUnary, nameRowUnary, structuralUnary,
      endpointUnary, transportRouteStructural, structuralNameEndpoint, gateLedgerNameRow,
      ledgerSameRequestGate, provenancePkg, endpointPkg⟩

end BEDC.Derived.ApophaticNameUp
