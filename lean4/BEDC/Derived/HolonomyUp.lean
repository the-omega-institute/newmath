import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HolonomyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HolonomyTransportPacket [AskSetup] [PackageSetup]
    (loop connection endpoint curvature ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory loop ∧ UnaryHistory connection ∧ UnaryHistory curvature ∧
    UnaryHistory ledger ∧ UnaryHistory provenance ∧ Cont loop connection endpoint ∧
      Cont curvature ledger provenance ∧ PkgSig bundle provenance pkg

theorem HolonomyTransportPacket_parallel_transport_stability [AskSetup] [PackageSetup]
    {loop loop' connection connection' endpoint endpoint' curvature curvature' ledger ledger'
      provenance provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportPacket loop connection endpoint curvature ledger provenance bundle pkg ->
      hsame loop loop' -> hsame connection connection' -> hsame endpoint endpoint' ->
        hsame curvature curvature' -> hsame ledger ledger' -> hsame provenance provenance' ->
          PkgSig bundle provenance' pkg ->
            HolonomyTransportPacket loop' connection' endpoint' curvature' ledger' provenance'
                bundle pkg ∧
              hsame endpoint endpoint' := by
  intro packet sameLoop sameConnection sameEndpoint sameCurvature sameLedger sameProvenance
    pkgSig'
  have loopUnary' : UnaryHistory loop' :=
    unary_transport packet.left sameLoop
  have connectionUnary' : UnaryHistory connection' :=
    unary_transport packet.right.left sameConnection
  have curvatureUnary' : UnaryHistory curvature' :=
    unary_transport packet.right.right.left sameCurvature
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport packet.right.right.right.left sameLedger
  have provenanceRow : Cont curvature ledger provenance :=
    packet.right.right.right.right.right.right.left
  have endpointRow' : Cont loop' connection' endpoint' :=
    cont_hsame_transport sameLoop sameConnection sameEndpoint
      packet.right.right.right.right.right.left
  have provenanceRow' : Cont curvature' ledger' provenance' :=
    cont_hsame_transport sameCurvature sameLedger sameProvenance provenanceRow
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed curvatureUnary' ledgerUnary' provenanceRow'
  exact
    And.intro
      (And.intro loopUnary'
        (And.intro connectionUnary'
          (And.intro curvatureUnary'
            (And.intro ledgerUnary'
              (And.intro provenanceUnary'
                (And.intro endpointRow'
                  (And.intro provenanceRow' pkgSig')))))))
      sameEndpoint

end BEDC.Derived.HolonomyUp
