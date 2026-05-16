import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_socket_citation_scope [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow citationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      Cont route provenance citationRead ->
        PkgSig bundle citationRead pkg ->
          UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory nameRow ∧ UnaryHistory citationRead ∧
                Cont socket request gate ∧ Cont request gate route ∧ Cont gate ledger route ∧
                  Cont gate ledger nameRow ∧ Cont route provenance citationRead ∧
                    hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle citationRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg hsame Cont
  intro carrier routeProvenanceCitation citationPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have citationUnary : UnaryHistory citationRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCitation
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, citationUnary, socketRequestGate, requestGateRoute,
      gateLedgerRoute, gateLedgerNameRow, routeProvenanceCitation, ledgerSameRequestGate,
      provenancePkg, citationPkg⟩

end BEDC.Derived.ApophaticNameUp
