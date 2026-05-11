import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NestedDyadicIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def NestedDyadicIntervalPacket [AskSetup] [PackageSetup]
    (first next schedule refinement provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory first ∧ UnaryHistory next ∧ UnaryHistory schedule ∧ UnaryHistory refinement ∧
    UnaryHistory provenance ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
      Cont first next refinement ∧ Cont schedule refinement endpoint ∧ PkgSig bundle endpoint pkg

theorem NestedDyadicIntervalPacket_window_transport [AskSetup] [PackageSetup]
    {first next schedule refinement provenance ledger endpoint first' next' schedule'
      refinement' provenance' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedDyadicIntervalPacket first next schedule refinement provenance ledger endpoint bundle pkg ->
      hsame first first' ->
        hsame next next' ->
          hsame schedule schedule' ->
            hsame provenance provenance' ->
              hsame ledger ledger' ->
                Cont first' next' refinement' ->
                  Cont schedule' refinement' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      NestedDyadicIntervalPacket first' next' schedule' refinement' provenance'
                          ledger' endpoint' bundle pkg ∧
                        hsame refinement refinement' ∧ hsame endpoint endpoint' := by
  intro packet sameFirst sameNext sameSchedule sameProvenance sameLedger
    targetRefinement targetEndpoint targetPkg
  have firstUnary : UnaryHistory first :=
    packet.left
  have nextUnary : UnaryHistory next :=
    packet.right.left
  have scheduleUnary : UnaryHistory schedule :=
    packet.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    packet.right.right.right.right.right.left
  have sourceRefinement : Cont first next refinement :=
    packet.right.right.right.right.right.right.right.left
  have sourceEndpoint : Cont schedule refinement endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have firstUnary' : UnaryHistory first' :=
    unary_transport firstUnary sameFirst
  have nextUnary' : UnaryHistory next' :=
    unary_transport nextUnary sameNext
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have refinementUnary' : UnaryHistory refinement' :=
    unary_cont_closed firstUnary' nextUnary' targetRefinement
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed scheduleUnary' refinementUnary' targetEndpoint
  have sameRefinement : hsame refinement refinement' :=
    cont_respects_hsame sameFirst sameNext sourceRefinement targetRefinement
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameSchedule sameRefinement sourceEndpoint targetEndpoint
  exact
    ⟨⟨firstUnary', nextUnary', scheduleUnary', refinementUnary', provenanceUnary',
        ledgerUnary', endpointUnary', targetRefinement, targetEndpoint, targetPkg⟩,
      sameRefinement, sameEndpoint⟩

theorem NestedDyadicIntervalPacket_singleton_chain_vacuity [AskSetup] [PackageSetup]
    {first schedule refinement provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedDyadicIntervalPacket first BHist.Empty schedule refinement provenance ledger endpoint
        bundle pkg →
      hsame refinement first ∧ UnaryHistory endpoint ∧ Cont schedule first endpoint ∧
        PkgSig bundle endpoint pkg := by
  intro packet
  have scheduleUnary : UnaryHistory schedule :=
    packet.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    packet.right.right.right.right.right.right.left
  have firstRefinement : Cont first BHist.Empty refinement :=
    packet.right.right.right.right.right.right.right.left
  have scheduleRefinement : Cont schedule refinement endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  have refinementEq : refinement = first := by
    exact Eq.trans firstRefinement (append_empty_right first)
  constructor
  · exact refinementEq
  · constructor
    · exact endpointUnary
    · constructor
      · cases refinementEq
        exact scheduleRefinement
      · exact pkgSig

end BEDC.Derived.NestedDyadicIntervalUp
