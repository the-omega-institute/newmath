import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_gate_source_compatibility [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      Cont socket request sourceRead →
        PkgSig bundle sourceRead pkg →
          UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory sourceRead ∧ Cont socket request gate ∧
              Cont socket request sourceRead ∧ Cont gate ledger nameRow ∧
                hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier socketRequestSource sourcePkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed socketUnary requestUnary socketRequestSource
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, sourceUnary, socketRequestGate,
      socketRequestSource, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg,
      sourcePkg⟩

end BEDC.Derived.ApophaticNameUp
