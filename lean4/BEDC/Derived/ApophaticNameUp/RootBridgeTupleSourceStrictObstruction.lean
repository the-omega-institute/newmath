import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_bridge_tuple_source_strict_obstruction
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead
      obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow downstreamRead →
        PkgSig bundle downstreamRead pkg →
          Cont downstreamRead ledger obstructionRead →
            PkgSig bundle obstructionRead pkg →
              UnaryHistory downstreamRead ∧ UnaryHistory obstructionRead ∧
                Cont ledger nameRow downstreamRead ∧
                  Cont downstreamRead ledger obstructionRead ∧
                    hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle downstreamRead pkg ∧
                        PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier ledgerNameDownstream downstreamPkg downstreamLedgerObstruction
    obstructionPkg
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameDownstream
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed downstreamUnary ledgerUnary downstreamLedgerObstruction
  exact
    ⟨downstreamUnary, obstructionUnary, ledgerNameDownstream,
      downstreamLedgerObstruction, ledgerSameRequestGate, provenancePkg, downstreamPkg,
      obstructionPkg⟩

end BEDC.Derived.ApophaticNameUp
