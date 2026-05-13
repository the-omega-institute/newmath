import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContinuationTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

structure ContinuationTracePacket [AskSetup] [PackageSetup] where
  source : BHist
  markTail : BHist
  target : BHist
  traceLedger : BHist
  transport : BHist
  continuation : BHist
  provenance : Pkg
  name : NameCert (fun row : BHist => hsame row target) hsame
  route_witness : Cont source markTail target
  source_transport : hsame source source
  target_transport : hsame target target

def ContinuationTraceCarrier [AskSetup] [PackageSetup]
    (source mark target ledger transports route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory mark ∧ UnaryHistory target ∧ UnaryHistory ledger ∧
    UnaryHistory transports ∧ UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
      Cont source mark target ∧ Cont target ledger route ∧ Cont route cert provenance ∧
        PkgSig bundle provenance pkg

theorem ContinuationTraceCarrier_small_step_readback [AskSetup] [PackageSetup]
    {source mark target ledger transports route provenance cert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationTraceCarrier source mark target ledger transports route provenance cert bundle
        pkg →
      Cont route cert consumer →
        UnaryHistory source ∧ UnaryHistory mark ∧ UnaryHistory target ∧ UnaryHistory consumer ∧
          Cont source mark target ∧ Cont target ledger route ∧ PkgSig bundle provenance pkg := by
  intro carrier consumerRow
  obtain ⟨sourceUnary, markUnary, targetUnary, _ledgerUnary, _transportsUnary, routeUnary,
    _provenanceUnary, certUnary, sourceMarkTargetRow, targetLedgerRouteRow, _routeCertProvenanceRow,
    pkgSig⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary certUnary consumerRow
  exact ⟨sourceUnary, markUnary, targetUnary, consumerUnary, sourceMarkTargetRow,
    targetLedgerRouteRow, pkgSig⟩

end BEDC.Derived.ContinuationTraceUp
