import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_boundary_request_nonescape [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance name boundaryRead refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance name bundle pkg →
      Cont socket request boundaryRead →
        Cont boundaryRead gate refusedRead →
          PkgSig bundle refusedRead pkg →
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory boundaryRead ∧ UnaryHistory refusedRead ∧
                Cont socket request boundaryRead ∧ Cont boundaryRead gate refusedRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle refusedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier socketRequestBoundary boundaryGateRefused refusedPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, _ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerName, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed socketUnary requestUnary socketRequestBoundary
  have refusedUnary : UnaryHistory refusedRead :=
    unary_cont_closed boundaryUnary gateUnary boundaryGateRefused
  exact
    ⟨socketUnary, requestUnary, gateUnary, boundaryUnary, refusedUnary,
      socketRequestBoundary, boundaryGateRefused, provenancePkg, refusedPkg⟩

end BEDC.Derived.ApophaticNameUp
