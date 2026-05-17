import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_socket_refusal_route_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead refusalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request socketRead →
        Cont gate ledger refusalRead →
          PkgSig bundle refusalRead pkg →
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory socketRead ∧ UnaryHistory refusalRead ∧
                Cont socket request socketRead ∧ Cont gate ledger refusalRead ∧
                  Cont gate ledger route ∧ hsame ledger (append request gate) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier socketReadRoute refusalReadRoute refusalReadPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate,
    _requestGateRoute, gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate,
    provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed socketUnary requestUnary socketReadRoute
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed gateUnary ledgerUnary refusalReadRoute
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, socketReadUnary, refusalReadUnary,
      socketReadRoute, refusalReadRoute, gateLedgerRoute, ledgerSameRequestGate,
      provenancePkg, refusalReadPkg⟩

end BEDC.Derived.ApophaticNameUp
