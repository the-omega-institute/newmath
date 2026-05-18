import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_externality_consumer_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger nameRow consumerRead ->
        PkgSig bundle consumerRead pkg ->
          UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory nameRow ∧ UnaryHistory consumerRead ∧
                Cont socket request gate ∧ Cont request gate route ∧ Cont gate ledger route ∧
                  Cont gate ledger nameRow ∧ Cont ledger nameRow consumerRead ∧
                    hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier ledgerNameConsumer consumerPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameConsumer
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, consumerUnary, socketRequestGate, requestGateRoute,
      gateLedgerRoute, gateLedgerNameRow, ledgerNameConsumer, ledgerSameRequestGate,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.ApophaticNameUp
