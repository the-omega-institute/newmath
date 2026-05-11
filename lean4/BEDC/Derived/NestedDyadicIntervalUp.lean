import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NestedDyadicIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem NestedDyadicIntervalPacket_public_finite_window_export [AskSetup] [PackageSetup]
    {first next schedule refinement provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedDyadicIntervalPacket first next schedule refinement provenance ledger endpoint
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            NestedDyadicIntervalPacket first next schedule refinement provenance ledger endpoint
                bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            NestedDyadicIntervalPacket first next schedule refinement provenance ledger endpoint
                bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            NestedDyadicIntervalPacket first next schedule refinement provenance ledger endpoint
                bundle pkg ∧ hsame row endpoint)
          hsame ∧
        UnaryHistory first ∧ UnaryHistory next ∧ UnaryHistory schedule ∧
          UnaryHistory refinement ∧ Cont first next refinement ∧
            Cont schedule refinement endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  let Surface : BHist -> Prop :=
    fun row : BHist =>
      NestedDyadicIntervalPacket first next schedule refinement provenance ledger endpoint
          bundle pkg ∧ hsame row endpoint
  have endpointSource : Surface endpoint :=
    And.intro packet (hsame_refl endpoint)
  have cert : SemanticNameCert Surface Surface Surface hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨cert, packet.left, packet.right.left, packet.right.right.left,
      packet.right.right.right.left, packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right⟩

theorem NestedDyadicIntervalPacket_empty_refinement_source [AskSetup] [PackageSetup]
    {first next schedule refinement provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedDyadicIntervalPacket first next schedule refinement provenance ledger endpoint
        bundle pkg ->
      hsame refinement BHist.Empty ->
        hsame first BHist.Empty ∧ hsame next BHist.Empty ∧ hsame endpoint schedule := by
  intro packet refinementEmpty
  have refinementRow : Cont first next refinement :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont schedule refinement endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have appendedEmpty : append first next = BHist.Empty :=
    refinementRow.symm.trans refinementEmpty
  have firstEmpty : hsame first BHist.Empty :=
    (append_eq_empty_iff.mp appendedEmpty).left
  have nextEmpty : hsame next BHist.Empty :=
    (append_eq_empty_iff.mp appendedEmpty).right
  have endpointSchedule : hsame endpoint schedule := by
    cases refinementEmpty
    exact endpointRow.trans (append_empty_right schedule)
  exact ⟨firstEmpty, nextEmpty, endpointSchedule⟩

def NestedDyadicIntervalClassifier [AskSetup] [PackageSetup]
    (first next schedule refinement provenance ledger endpoint first' next' schedule'
      refinement' provenance' ledger' endpoint' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  NestedDyadicIntervalPacket first next schedule refinement provenance ledger endpoint bundle pkg ∧
    NestedDyadicIntervalPacket first' next' schedule' refinement' provenance' ledger' endpoint'
        bundle pkg ∧
      hsame first first' ∧ hsame next next' ∧ hsame schedule schedule' ∧
        hsame refinement refinement' ∧ hsame provenance provenance' ∧
          hsame ledger ledger' ∧ hsame endpoint endpoint'

theorem NestedDyadicIntervalPacket_shared_prefix_handoff [AskSetup] [PackageSetup]
    {first next schedule refinement provenance ledger endpoint first' next' schedule'
      refinement' provenance' ledger' endpoint' sharedSchedule sharedRefinement
      sharedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedDyadicIntervalClassifier first next schedule refinement provenance ledger endpoint
        first' next' schedule' refinement' provenance' ledger' endpoint' bundle pkg ->
      hsame schedule sharedSchedule ->
        hsame refinement sharedRefinement ->
          Cont sharedSchedule sharedRefinement sharedEndpoint ->
            PkgSig bundle sharedEndpoint pkg ->
              hsame endpoint sharedEndpoint ∧ hsame endpoint' sharedEndpoint ∧
                PkgSig bundle sharedEndpoint pkg := by
  intro classifier sameSchedule sameRefinement sharedEndpointRoute sharedEndpointPkg
  have leftPacket :
      NestedDyadicIntervalPacket first next schedule refinement provenance ledger endpoint
        bundle pkg :=
    classifier.left
  have rightPacket :
      NestedDyadicIntervalPacket first' next' schedule' refinement' provenance' ledger'
        endpoint' bundle pkg :=
    classifier.right.left
  have sameScheduleRows : hsame schedule schedule' :=
    classifier.right.right.right.right.left
  have sameRefinementRows : hsame refinement refinement' :=
    classifier.right.right.right.right.right.left
  have leftEndpointRoute : Cont schedule refinement endpoint :=
    leftPacket.right.right.right.right.right.right.right.right.left
  have rightEndpointRoute : Cont schedule' refinement' endpoint' :=
    rightPacket.right.right.right.right.right.right.right.right.left
  have sameEndpoint : hsame endpoint sharedEndpoint :=
    cont_respects_hsame sameSchedule sameRefinement leftEndpointRoute sharedEndpointRoute
  have sameScheduleRight : hsame schedule' sharedSchedule :=
    hsame_trans (hsame_symm sameScheduleRows) sameSchedule
  have sameRefinementRight : hsame refinement' sharedRefinement :=
    hsame_trans (hsame_symm sameRefinementRows) sameRefinement
  have sameEndpointRight : hsame endpoint' sharedEndpoint :=
    cont_respects_hsame sameScheduleRight sameRefinementRight rightEndpointRoute
      sharedEndpointRoute
  exact ⟨sameEndpoint, sameEndpointRight, sharedEndpointPkg⟩

theorem NestedDyadicIntervalPacket_prefix_truncation_stability [AskSetup] [PackageSetup]
    {first next schedule refinement provenance ledger endpoint cut firstCut nextCut scheduleCut
      refinementCut ledgerCut endpointCut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedDyadicIntervalPacket first next schedule refinement provenance ledger endpoint
        bundle pkg ->
      UnaryHistory cut ->
        Cont first cut firstCut ->
          Cont next cut nextCut ->
            Cont schedule cut scheduleCut ->
              Cont ledger cut ledgerCut ->
                Cont firstCut nextCut refinementCut ->
                  Cont scheduleCut refinementCut endpointCut ->
                    PkgSig bundle endpointCut pkg ->
                      NestedDyadicIntervalPacket firstCut nextCut scheduleCut refinementCut
                        provenance ledgerCut endpointCut bundle pkg := by
  intro packet cutUnary firstCutRow nextCutRow scheduleCutRow ledgerCutRow refinementCutRow
    endpointCutRow endpointCutPkg
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
  have firstCutUnary : UnaryHistory firstCut :=
    unary_cont_closed firstUnary cutUnary firstCutRow
  have nextCutUnary : UnaryHistory nextCut :=
    unary_cont_closed nextUnary cutUnary nextCutRow
  have scheduleCutUnary : UnaryHistory scheduleCut :=
    unary_cont_closed scheduleUnary cutUnary scheduleCutRow
  have ledgerCutUnary : UnaryHistory ledgerCut :=
    unary_cont_closed ledgerUnary cutUnary ledgerCutRow
  have refinementCutUnary : UnaryHistory refinementCut :=
    unary_cont_closed firstCutUnary nextCutUnary refinementCutRow
  have endpointCutUnary : UnaryHistory endpointCut :=
    unary_cont_closed scheduleCutUnary refinementCutUnary endpointCutRow
  exact
    ⟨firstCutUnary, nextCutUnary, scheduleCutUnary, refinementCutUnary, provenanceUnary,
      ledgerCutUnary, endpointCutUnary, refinementCutRow, endpointCutRow, endpointCutPkg⟩

end BEDC.Derived.NestedDyadicIntervalUp
