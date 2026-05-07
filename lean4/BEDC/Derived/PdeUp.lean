import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.PdeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PdeRelationClassifier
    (manifold derivative relation boundary provenance : BHist) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory derivative ∧ UnaryHistory boundary ∧
    Cont manifold derivative relation ∧ Cont relation boundary provenance

theorem PdeRelationClassifier_endpoint_transport
    {manifold manifold' derivative derivative' relation relation' boundary boundary' provenance
      provenance' : BHist} :
    PdeRelationClassifier manifold derivative relation boundary provenance ->
      hsame manifold manifold' -> hsame derivative derivative' -> hsame boundary boundary' ->
        Cont manifold' derivative' relation' -> Cont relation' boundary' provenance' ->
          PdeRelationClassifier manifold' derivative' relation' boundary' provenance' ∧
            hsame relation relation' ∧ hsame provenance provenance' := by
  intro rows sameManifold sameDerivative sameBoundary transportedRelation transportedProvenance
  have relationSame : hsame relation relation' :=
    cont_respects_hsame sameManifold sameDerivative rows.right.right.right.left
      transportedRelation
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame relationSame sameBoundary rows.right.right.right.right
      transportedProvenance
  have transportedRows :
      PdeRelationClassifier manifold' derivative' relation' boundary' provenance' :=
    And.intro (unary_transport rows.left sameManifold)
      (And.intro (unary_transport rows.right.left sameDerivative)
        (And.intro (unary_transport rows.right.right.left sameBoundary)
          (And.intro transportedRelation transportedProvenance)))
  exact And.intro transportedRows (And.intro relationSame provenanceSame)

theorem PdeRelationClassifier_visible_append_surface
    {manifold derivative relation boundary provenance : BHist} :
    PdeRelationClassifier manifold derivative relation boundary provenance ->
      hsame provenance (append relation boundary) ∧
        hsame provenance (append (append manifold derivative) boundary) ∧
          hsame provenance (append manifold (append derivative boundary)) := by
  intro rows
  have relationReadback : hsame relation (append manifold derivative) :=
    rows.right.right.right.left
  have provenanceReadback : hsame provenance (append relation boundary) :=
    rows.right.right.right.right
  have endpointReadback :
      hsame provenance (append (append manifold derivative) boundary) :=
    provenanceReadback.trans
      (congrArg (fun source => append source boundary) relationReadback)
  exact And.intro provenanceReadback
    (And.intro endpointReadback
      (endpointReadback.trans (append_assoc manifold derivative boundary)))

def PdeCarriedSourceRow [AskSetup] [PackageSetup]
    (manifold derivative relation boundary endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory derivative ∧ UnaryHistory boundary ∧
    Cont manifold derivative relation ∧ Cont relation boundary endpoint ∧
      PkgSig bundle endpoint pkg

theorem PdeCarriedSourceRow_carrier_obligation [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      UnaryHistory relation ∧ UnaryHistory endpoint ∧ Cont manifold derivative relation ∧
        Cont relation boundary endpoint ∧ PkgSig bundle endpoint pkg := by
  intro row
  have relationUnary : UnaryHistory relation :=
    unary_cont_closed row.left row.right.left row.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed relationUnary row.right.right.left row.right.right.right.right.left
  exact And.intro relationUnary
    (And.intro endpointUnary
      (And.intro row.right.right.right.left
        (And.intro row.right.right.right.right.left row.right.right.right.right.right)))

theorem PdeCarriedSourceRow_classifier_obligation [AskSetup] [PackageSetup]
    {manifold manifold' derivative derivative' relation relation' boundary boundary'
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      UnaryHistory manifold' -> UnaryHistory derivative' -> UnaryHistory boundary' ->
        hsame manifold manifold' -> hsame derivative derivative' -> hsame boundary boundary' ->
          Cont manifold' derivative' relation' -> Cont relation' boundary' endpoint' ->
            UnaryHistory relation' ∧ UnaryHistory endpoint' ∧
              hsame relation relation' ∧ hsame endpoint endpoint' := by
  intro row manifoldUnary' derivativeUnary' boundaryUnary' sameManifold sameDerivative
    sameBoundary relationCont' endpointCont'
  have relationUnary' : UnaryHistory relation' :=
    unary_cont_closed manifoldUnary' derivativeUnary' relationCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed relationUnary' boundaryUnary' endpointCont'
  have sameRelation : hsame relation relation' :=
    cont_respects_hsame sameManifold sameDerivative row.right.right.right.left relationCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRelation sameBoundary row.right.right.right.right.left endpointCont'
  exact And.intro relationUnary'
    (And.intro endpointUnary' (And.intro sameRelation sameEndpoint))

theorem PdeCarriedSourceRow_ledger_exactness_surface
    {manifold derivative relation boundary relationBoundary endpoint : BHist} :
    UnaryHistory manifold -> UnaryHistory derivative -> UnaryHistory relation ->
      UnaryHistory boundary -> Cont relation boundary relationBoundary ->
        Cont (append manifold derivative) relationBoundary endpoint ->
          UnaryHistory relationBoundary ∧ UnaryHistory endpoint ∧
            Cont relation boundary relationBoundary ∧
              Cont (append manifold derivative) relationBoundary endpoint := by
  intro manifoldUnary derivativeUnary relationUnary boundaryUnary relationBoundaryCont endpointCont
  have relationBoundaryUnary : UnaryHistory relationBoundary :=
    unary_cont_closed relationUnary boundaryUnary relationBoundaryCont
  have manifoldDerivativeUnary : UnaryHistory (append manifold derivative) :=
    unary_append_closed manifoldUnary derivativeUnary
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed manifoldDerivativeUnary relationBoundaryUnary endpointCont
  exact And.intro relationBoundaryUnary
    (And.intro endpointUnary (And.intro relationBoundaryCont endpointCont))

theorem PdeCarriedSourceRow_carrier_obligation_surface
    {manifold derivative relation boundary relationBoundary endpoint : BHist} :
    UnaryHistory manifold -> UnaryHistory derivative -> UnaryHistory relation ->
      UnaryHistory boundary -> Cont relation boundary relationBoundary ->
        Cont (append manifold derivative) relationBoundary endpoint ->
          UnaryHistory manifold ∧ UnaryHistory derivative ∧ UnaryHistory relation ∧
            UnaryHistory boundary ∧ UnaryHistory relationBoundary ∧ UnaryHistory endpoint ∧
              Cont relation boundary relationBoundary ∧
                Cont (append manifold derivative) relationBoundary endpoint := by
  intro manifoldUnary derivativeUnary relationUnary boundaryUnary relationBoundaryCont endpointCont
  have relationBoundaryUnary : UnaryHistory relationBoundary :=
    unary_cont_closed relationUnary boundaryUnary relationBoundaryCont
  have manifoldDerivativeUnary : UnaryHistory (append manifold derivative) :=
    unary_append_closed manifoldUnary derivativeUnary
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed manifoldDerivativeUnary relationBoundaryUnary endpointCont
  exact And.intro manifoldUnary
    (And.intro derivativeUnary
      (And.intro relationUnary
        (And.intro boundaryUnary
          (And.intro relationBoundaryUnary
            (And.intro endpointUnary
              (And.intro relationBoundaryCont endpointCont))))))

theorem PdeCarriedSourceRow_stability_ledger_exactness_obligation_surface
    {manifold derivative relation boundary relationBoundary endpoint
      manifold' derivative' relation' boundary' relationBoundary' endpoint' : BHist} :
    UnaryHistory manifold' -> UnaryHistory derivative' -> UnaryHistory relation' ->
      UnaryHistory boundary' -> hsame manifold manifold' -> hsame derivative derivative' ->
        hsame relation relation' -> hsame boundary boundary' ->
          Cont relation boundary relationBoundary ->
            Cont relation' boundary' relationBoundary' ->
              Cont (append manifold derivative) relationBoundary endpoint ->
                Cont (append manifold' derivative') relationBoundary' endpoint' ->
                  UnaryHistory relationBoundary' ∧ UnaryHistory endpoint' ∧
                    hsame relationBoundary relationBoundary' ∧ hsame endpoint endpoint' ∧
                      Cont relation' boundary' relationBoundary' ∧
                        Cont (append manifold' derivative') relationBoundary' endpoint' := by
  intro manifoldUnary derivativeUnary relationUnary boundaryUnary
  intro manifoldSame derivativeSame relationSame boundarySame
  intro relationBoundaryCont relationBoundaryCont' endpointCont endpointCont'
  have relationBoundaryUnary : UnaryHistory relationBoundary' :=
    unary_cont_closed relationUnary boundaryUnary relationBoundaryCont'
  have sourceSame : hsame (append manifold derivative) (append manifold' derivative') := by
    cases manifoldSame
    cases derivativeSame
    rfl
  have relationBoundarySame : hsame relationBoundary relationBoundary' :=
    cont_respects_hsame relationSame boundarySame relationBoundaryCont relationBoundaryCont'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame sourceSame relationBoundarySame endpointCont endpointCont'
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed
      (unary_append_closed manifoldUnary derivativeUnary)
      relationBoundaryUnary
      endpointCont'
  exact And.intro relationBoundaryUnary
    (And.intro endpointUnary
      (And.intro relationBoundarySame
        (And.intro endpointSame (And.intro relationBoundaryCont' endpointCont'))))

theorem PdeCarriedSourceRow_stability_ledger_exactness_obligation [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint relationBoundary summarizedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      Cont relation boundary relationBoundary ->
        Cont (append manifold derivative) relationBoundary summarizedEndpoint ->
          UnaryHistory relationBoundary ∧ UnaryHistory summarizedEndpoint ∧
            hsame relationBoundary endpoint ∧ Cont relation boundary relationBoundary ∧
              Cont (append manifold derivative) relationBoundary summarizedEndpoint ∧
                PkgSig bundle endpoint pkg := by
  intro row relationBoundaryCont summarizedEndpointCont
  have relationUnary : UnaryHistory relation :=
    unary_cont_closed row.left row.right.left row.right.right.right.left
  have relationBoundaryUnary : UnaryHistory relationBoundary :=
    unary_cont_closed relationUnary row.right.right.left relationBoundaryCont
  have manifoldDerivativeUnary : UnaryHistory (append manifold derivative) :=
    unary_append_closed row.left row.right.left
  have summarizedEndpointUnary : UnaryHistory summarizedEndpoint :=
    unary_cont_closed manifoldDerivativeUnary relationBoundaryUnary summarizedEndpointCont
  have sameEndpoint : hsame relationBoundary endpoint :=
    cont_deterministic relationBoundaryCont row.right.right.right.right.left
  exact And.intro relationBoundaryUnary
      (And.intro summarizedEndpointUnary
        (And.intro sameEndpoint
          (And.intro relationBoundaryCont
            (And.intro summarizedEndpointCont row.right.right.right.right.right))))

theorem PdeStabilityLedger_relation_boundary_append_surface
    {manifold derivative relation boundary relationBoundary endpoint : BHist} :
    UnaryHistory manifold -> UnaryHistory derivative -> UnaryHistory relation ->
      UnaryHistory boundary -> Cont relation boundary relationBoundary ->
        Cont (append manifold derivative) relationBoundary endpoint ->
          hsame relationBoundary (append relation boundary) ∧
            hsame endpoint (append (append manifold derivative) (append relation boundary)) ∧
              UnaryHistory endpoint := by
  intro manifoldUnary derivativeUnary relationUnary boundaryUnary relationBoundaryCont endpointCont
  have relationBoundaryUnary : UnaryHistory relationBoundary :=
    unary_cont_closed relationUnary boundaryUnary relationBoundaryCont
  have manifoldDerivativeUnary : UnaryHistory (append manifold derivative) :=
    unary_append_closed manifoldUnary derivativeUnary
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed manifoldDerivativeUnary relationBoundaryUnary endpointCont
  have endpointReadback :
      hsame endpoint (append (append manifold derivative) (append relation boundary)) :=
    endpointCont.trans
      (congrArg (fun surface => append (append manifold derivative) surface)
        relationBoundaryCont)
  exact And.intro relationBoundaryCont (And.intro endpointReadback endpointUnary)

end BEDC.Derived.PdeUp
