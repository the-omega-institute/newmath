import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_route_exhaustion [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow gateRead ledgerRead exported
      : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      Cont request gate gateRead ->
        Cont gateRead ledger ledgerRead ->
          Cont ledgerRead nameRow exported ->
            PkgSig bundle exported pkg ->
              UnaryHistory request ∧ UnaryHistory gate ∧ UnaryHistory ledger ∧
                UnaryHistory nameRow ∧ UnaryHistory gateRead ∧ UnaryHistory ledgerRead ∧
                  UnaryHistory exported ∧ Cont request gate gateRead ∧
                    Cont gateRead ledger ledgerRead ∧ Cont ledgerRead nameRow exported ∧
                      hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle hsame UnaryHistory
  intro carrier requestGateRead gateReadLedgerRead ledgerReadNameExported exportedPkg
  obtain ⟨_socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed requestUnary gateUnary requestGateRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed gateReadUnary ledgerUnary gateReadLedgerRead
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed ledgerReadUnary nameRowUnary ledgerReadNameExported
  exact
    ⟨requestUnary, gateUnary, ledgerUnary, nameRowUnary, gateReadUnary, ledgerReadUnary,
      exportedUnary, requestGateRead, gateReadLedgerRead, ledgerReadNameExported,
      ledgerSameRequestGate, provenancePkg, exportedPkg⟩

end BEDC.Derived.ApophaticNameUp
