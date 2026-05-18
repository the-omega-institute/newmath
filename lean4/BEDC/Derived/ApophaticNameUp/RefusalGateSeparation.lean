import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_gate_separation [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow gateRead separationRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont socket request gateRead ->
        Cont gateRead ledger separationRead ->
          PkgSig bundle separationRead pkg ->
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory gateRead ∧ UnaryHistory separationRead ∧
                Cont socket request gate ∧ Cont socket request gateRead ∧
                  Cont gateRead ledger separationRead ∧ hsame ledger (append request gate) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle separationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier gateReadRoute separationRoute separationPkg
  rcases carrier with
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
      _provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
      _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed socketUnary requestUnary gateReadRoute
  have separationReadUnary : UnaryHistory separationRead :=
    unary_cont_closed gateReadUnary ledgerUnary separationRoute
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, gateReadUnary, separationReadUnary,
      socketRequestGate, gateReadRoute, separationRoute, ledgerSameRequestGate, provenancePkg,
      separationPkg⟩

end BEDC.Derived.ApophaticNameUp
