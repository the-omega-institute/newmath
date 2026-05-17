import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_downstream_boundary_exactness [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance name boundaryRead refusedRead downstream :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance name bundle pkg →
      Cont socket request boundaryRead →
        Cont boundaryRead gate refusedRead →
          Cont refusedRead ledger downstream →
            PkgSig bundle downstream pkg →
              UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
                UnaryHistory ledger ∧ UnaryHistory boundaryRead ∧
                  UnaryHistory refusedRead ∧ UnaryHistory downstream ∧
                    Cont socket request boundaryRead ∧ Cont boundaryRead gate refusedRead ∧
                      Cont refusedRead ledger downstream ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier socketRequestBoundary boundaryGateRefused refusedLedgerDownstream downstreamPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerName, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed socketUnary requestUnary socketRequestBoundary
  have refusedUnary : UnaryHistory refusedRead :=
    unary_cont_closed boundaryUnary gateUnary boundaryGateRefused
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed refusedUnary ledgerUnary refusedLedgerDownstream
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, boundaryUnary, refusedUnary,
      downstreamUnary, socketRequestBoundary, boundaryGateRefused, refusedLedgerDownstream,
      provenancePkg, downstreamPkg⟩

end BEDC.Derived.ApophaticNameUp
