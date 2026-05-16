import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_boundary_request_obligation_triad [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead requestRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request socketRead →
        Cont request gate requestRead →
          PkgSig bundle requestRead pkg →
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory socketRead ∧ UnaryHistory requestRead ∧
                Cont socket request gate ∧ Cont socket request socketRead ∧
                  Cont request gate requestRead ∧ hsame ledger (append request gate) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle requestRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier socketRequestRead requestGateRead requestReadPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, _ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed socketUnary requestUnary socketRequestRead
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed requestUnary gateUnary requestGateRead
  exact
    ⟨socketUnary, requestUnary, gateUnary, socketReadUnary, requestReadUnary,
      socketRequestGate, socketRequestRead, requestGateRead, ledgerSameRequestGate,
      provenancePkg, requestReadPkg⟩

end BEDC.Derived.ApophaticNameUp
