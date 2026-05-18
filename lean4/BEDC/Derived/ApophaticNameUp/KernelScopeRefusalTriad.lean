import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_kernel_scope_refusal_triad [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont socket request gate ->
        Cont gate ledger kernelRead ->
          PkgSig bundle kernelRead pkg ->
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory kernelRead ∧ Cont socket request gate ∧
                Cont gate ledger kernelRead ∧ hsame ledger (append request gate) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle kernelRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame PkgSig
  intro carrier socketRequestGateArg gateLedgerKernel kernelPkg
  rcases carrier with
    ⟨socketUnary, requestUnary, _gateUnary, ledgerUnary, _transportUnary, _routeUnary,
      _provenanceUnary, _nameRowUnary, _carrierSocketRequestGate, _requestGateRoute,
      _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩
  have gateUnary : UnaryHistory gate :=
    unary_cont_closed socketUnary requestUnary socketRequestGateArg
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerKernel
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, kernelUnary,
      socketRequestGateArg, gateLedgerKernel, ledgerSameRequestGate, provenancePkg,
      kernelPkg⟩

end BEDC.Derived.ApophaticNameUp
