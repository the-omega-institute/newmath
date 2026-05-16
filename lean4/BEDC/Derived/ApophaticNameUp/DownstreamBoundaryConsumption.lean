import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_downstream_boundary_consumption [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow boundaryRead downstreamRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow boundaryRead →
        Cont boundaryRead provenance downstreamRead →
          PkgSig bundle downstreamRead pkg →
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory provenance ∧ UnaryHistory boundaryRead ∧
                UnaryHistory downstreamRead ∧ Cont socket request gate ∧
                  Cont gate ledger nameRow ∧ Cont ledger nameRow boundaryRead ∧
                    Cont boundaryRead provenance downstreamRead ∧
                      hsame ledger (append request gate) ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier ledgerNameBoundary boundaryProvenanceDownstream downstreamPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameBoundary
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed boundaryUnary provenanceUnary boundaryProvenanceDownstream
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, provenanceUnary, boundaryUnary,
      downstreamUnary, socketRequestGate, gateLedgerNameRow, ledgerNameBoundary,
      boundaryProvenanceDownstream, ledgerSameRequestGate, provenancePkg, downstreamPkg⟩

end BEDC.Derived.ApophaticNameUp
