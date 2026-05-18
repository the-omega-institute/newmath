import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_consumer_socket_request_totality
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger nameRow rootRead ->
        PkgSig bundle rootRead pkg ->
          UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory nameRow ∧ UnaryHistory rootRead ∧
                Cont socket request gate ∧ Cont request gate route ∧ Cont gate ledger route ∧
                  Cont gate ledger nameRow ∧ Cont ledger nameRow rootRead ∧
                    hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier ledgerNameRoot rootPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRoot
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, rootUnary, socketRequestGate, requestGateRoute,
      gateLedgerRoute, gateLedgerNameRow, ledgerNameRoot, ledgerSameRequestGate,
      provenancePkg, rootPkg⟩

end BEDC.Derived.ApophaticNameUp
