import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_ledger_coverage [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow ledgerRead citationRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger nameRow ledgerRead ->
        Cont ledgerRead route citationRead ->
          PkgSig bundle citationRead pkg ->
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory route ∧ UnaryHistory nameRow ∧
                UnaryHistory ledgerRead ∧ UnaryHistory citationRead ∧
                  Cont socket request gate ∧ Cont request gate route ∧
                    Cont gate ledger route ∧ Cont gate ledger nameRow ∧
                      Cont ledger nameRow ledgerRead ∧
                        Cont ledgerRead route citationRead ∧
                          hsame ledger (append request gate) ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle citationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier ledgerNameRead readRouteCitation citationPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRead
  have citationReadUnary : UnaryHistory citationRead :=
    unary_cont_closed ledgerReadUnary routeUnary readRouteCitation
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, routeUnary, nameRowUnary,
      ledgerReadUnary, citationReadUnary, socketRequestGate, requestGateRoute,
      gateLedgerRoute, gateLedgerNameRow, ledgerNameRead, readRouteCitation,
      ledgerSameRequestGate, provenancePkg, citationPkg⟩

end BEDC.Derived.ApophaticNameUp
