import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_boundary_citation_exhaustion [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow citation endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      Cont ledger nameRow citation ->
        Cont citation provenance endpoint ->
          PkgSig bundle endpoint pkg ->
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory citation ∧ UnaryHistory endpoint ∧
                Cont socket request gate ∧ Cont gate ledger nameRow ∧
                  Cont ledger nameRow citation ∧ Cont citation provenance endpoint ∧
                    hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier ledgerNameCitation citationProvenanceEndpoint endpointPkg
  rcases carrier with
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
      provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute, _gateLedgerRoute,
      gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩
  have citationUnary : UnaryHistory citation :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameCitation
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed citationUnary provenanceUnary citationProvenanceEndpoint
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, citationUnary, endpointUnary,
      socketRequestGate, gateLedgerNameRow, ledgerNameCitation, citationProvenanceEndpoint,
      ledgerSameRequestGate, provenancePkg, endpointPkg⟩

end BEDC.Derived.ApophaticNameUp
