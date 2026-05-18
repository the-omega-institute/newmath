import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_socket_request_gate_factorization [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow requestRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      Cont socket request requestRead ->
        Cont requestRead gate publicRead ->
          PkgSig bundle publicRead pkg ->
            UnaryHistory requestRead ∧ UnaryHistory publicRead ∧
              Cont socket request requestRead ∧ Cont requestRead gate publicRead ∧
                hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier socketRequestRead requestReadGatePublic publicPkg
  rcases carrier with
    ⟨socketUnary, requestUnary, gateUnary, _ledgerUnary, _transportUnary, _routeUnary,
      _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
      _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed socketUnary requestUnary socketRequestRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed requestReadUnary gateUnary requestReadGatePublic
  exact
    ⟨requestReadUnary, publicReadUnary, socketRequestRead, requestReadGatePublic,
      ledgerSameRequestGate, provenancePkg, publicPkg⟩

end BEDC.Derived.ApophaticNameUp
