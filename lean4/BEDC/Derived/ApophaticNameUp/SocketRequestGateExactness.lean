import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_socket_request_gate_exactness [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead gateRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont socket request socketRead ->
        Cont request gate gateRead ->
          Cont gateRead ledger publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory socketRead ∧ UnaryHistory gateRead ∧ UnaryHistory publicRead ∧
                hsame ledger (append request gate) ∧ Cont socket request socketRead ∧
                  Cont request gate gateRead ∧ Cont gateRead ledger publicRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier socketRequestRead requestGateRead gateLedgerPublic publicPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed socketUnary requestUnary socketRequestRead
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed requestUnary gateUnary requestGateRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed gateReadUnary ledgerUnary gateLedgerPublic
  exact
    ⟨socketReadUnary, gateReadUnary, publicReadUnary, ledgerSameRequestGate,
      socketRequestRead, requestGateRead, gateLedgerPublic, provenancePkg, publicPkg⟩

end BEDC.Derived.ApophaticNameUp
