import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.PdeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem PdeBoundaryData_relation_transport_surface [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint boundary' boundaryEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      hsame boundary boundary' -> Cont relation boundary' boundaryEndpoint ->
        UnaryHistory boundaryEndpoint ∧ hsame endpoint boundaryEndpoint ∧
          PkgSig bundle endpoint pkg ∧ Cont relation boundary' boundaryEndpoint := by
  intro row sameBoundary boundaryCont'
  have relationUnary : UnaryHistory relation :=
    unary_cont_closed row.left row.right.left row.right.right.right.left
  have boundaryUnary' : UnaryHistory boundary' :=
    unary_transport row.right.right.left sameBoundary
  have boundaryEndpointUnary : UnaryHistory boundaryEndpoint :=
    unary_cont_closed relationUnary boundaryUnary' boundaryCont'
  have sameEndpoint : hsame endpoint boundaryEndpoint :=
    cont_respects_hsame (hsame_refl relation) sameBoundary
      row.right.right.right.right.left boundaryCont'
  exact And.intro boundaryEndpointUnary
    (And.intro sameEndpoint
      (And.intro row.right.right.right.right.right boundaryCont'))

theorem PdeCarriedSourceRow_visible_source_readback [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      hsame relation (append manifold derivative) ∧
        hsame endpoint (append (append manifold derivative) boundary) ∧
          UnaryHistory endpoint ∧ PkgSig bundle endpoint pkg := by
  intro row
  have obligation :=
    PdeCarriedSourceRow_carrier_obligation row
  have relationReadback : hsame relation (append manifold derivative) :=
    obligation.right.right.left
  have endpointReadback : hsame endpoint (append (append manifold derivative) boundary) :=
    obligation.right.right.right.left.trans
      (congrArg (fun source => append source boundary) relationReadback)
  exact And.intro relationReadback
    (And.intro endpointReadback
      (And.intro obligation.right.left obligation.right.right.right.right))

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

theorem PdeRelationClassifier_boundary_transport_surface
    {manifold manifold' derivative derivative' relation relation' boundary boundary' provenance
      provenance' : BHist} :
    PdeRelationClassifier manifold derivative relation boundary provenance ->
      hsame manifold manifold' -> hsame derivative derivative' -> hsame boundary boundary' ->
        Cont manifold' derivative' relation' -> Cont relation' boundary' provenance' ->
          hsame provenance (append relation boundary) ∧
            hsame provenance' (append relation' boundary') ∧
              PdeRelationClassifier manifold' derivative' relation' boundary' provenance' ∧
                hsame provenance provenance' := by
  intro rows sameManifold sameDerivative sameBoundary transportedRelation transportedProvenance
  have transported :=
    PdeRelationClassifier_endpoint_transport rows sameManifold sameDerivative sameBoundary
      transportedRelation transportedProvenance
  have sourceReadback : hsame provenance (append relation boundary) :=
    rows.right.right.right.right
  have transportedReadback : hsame provenance' (append relation' boundary') :=
    transportedProvenance
  exact And.intro sourceReadback
    (And.intro transportedReadback
      (And.intro transported.left transported.right.right))

theorem PdePublicInterface_export [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint relationBoundary summarizedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      Cont relation boundary relationBoundary ->
        Cont (append manifold derivative) relationBoundary summarizedEndpoint ->
          PdeRelationClassifier manifold derivative relation boundary endpoint ∧
            UnaryHistory relationBoundary ∧ UnaryHistory summarizedEndpoint ∧
              hsame relationBoundary endpoint ∧ PkgSig bundle endpoint pkg := by
  intro row relationBoundaryCont summarizedEndpointCont
  have relationClassifier : PdeRelationClassifier manifold derivative relation boundary endpoint :=
    And.intro row.left
      (And.intro row.right.left
        (And.intro row.right.right.left
          (And.intro row.right.right.right.left row.right.right.right.right.left)))
  have ledgerRows :=
    PdeCarriedSourceRow_stability_ledger_exactness_obligation row relationBoundaryCont
      summarizedEndpointCont
  exact And.intro relationClassifier
    (And.intro ledgerRows.left
      (And.intro ledgerRows.right.left
        (And.intro ledgerRows.right.right.left ledgerRows.right.right.right.right.right)))

theorem PdeConservativeStandardBridge_rows [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint relationBoundary summarizedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      Cont relation boundary relationBoundary ->
        Cont (append manifold derivative) relationBoundary summarizedEndpoint ->
          PdeRelationClassifier manifold derivative relation boundary endpoint ∧
            PkgSig bundle endpoint pkg ∧ UnaryHistory relationBoundary ∧
              UnaryHistory summarizedEndpoint ∧ hsame relationBoundary endpoint ∧
                hsame summarizedEndpoint (append (append manifold derivative) relationBoundary) := by
  intro row relationBoundaryCont summarizedEndpointCont
  have publicRows :=
    PdePublicInterface_export row relationBoundaryCont summarizedEndpointCont
  have summarizedReadback :
      hsame summarizedEndpoint (append (append manifold derivative) relationBoundary) :=
    summarizedEndpointCont
  exact And.intro publicRows.left
    (And.intro publicRows.right.right.right.right
      (And.intro publicRows.right.left
        (And.intro publicRows.right.right.left
          (And.intro publicRows.right.right.right.left summarizedReadback))))

theorem PdeConservativeStandardBridge_endpoint_readback [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint relationBoundary summarizedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      Cont relation boundary relationBoundary ->
        Cont (append manifold derivative) relationBoundary summarizedEndpoint ->
          hsame summarizedEndpoint (append (append manifold derivative) endpoint) := by
  intro row relationBoundaryCont summarizedEndpointCont
  have bridgeRows :=
    PdeConservativeStandardBridge_rows row relationBoundaryCont summarizedEndpointCont
  have sameBoundaryEndpoint : hsame relationBoundary endpoint :=
    bridgeRows.right.right.right.right.left
  exact
    cont_respects_hsame (hsame_refl (append manifold derivative)) sameBoundaryEndpoint
      summarizedEndpointCont (cont_intro rfl)

theorem PdePublicInterface_export_semantic_name_certificate [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      PdeRelationClassifier manifold derivative relation boundary endpoint ∧
        SemanticNameCert
          (fun h : BHist =>
            PdeCarriedSourceRow manifold derivative relation boundary h bundle pkg)
          (fun h : BHist =>
            PdeCarriedSourceRow manifold derivative relation boundary h bundle pkg)
          (fun h : BHist =>
            PdeCarriedSourceRow manifold derivative relation boundary h bundle pkg)
          (fun left right : BHist =>
            PdeCarriedSourceRow manifold derivative relation boundary left bundle pkg ∧
              PdeCarriedSourceRow manifold derivative relation boundary right bundle pkg ∧
                hsame left right) := by
  intro row
  have classifier : PdeRelationClassifier manifold derivative relation boundary endpoint :=
    And.intro row.left
      (And.intro row.right.left
        (And.intro row.right.right.left
          (And.intro row.right.right.right.left row.right.right.right.right.left)))
  let SourceSpec : BHist -> Prop := fun h : BHist =>
    PdeCarriedSourceRow manifold derivative relation boundary h bundle pkg
  let ClassifierSpec : BHist -> BHist -> Prop := fun left right : BHist =>
    SourceSpec left ∧ SourceSpec right ∧ hsame left right
  have core : NameCert SourceSpec ClassifierSpec := {
    carrier_inhabited := Exists.intro endpoint row
    equiv_refl := by
      intro h source
      exact And.intro source (And.intro source (hsame_refl h))
    equiv_symm := by
      intro h k classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    equiv_trans := by
      intro h k r classifiedHK classifiedKR
      exact And.intro classifiedHK.left
        (And.intro classifiedKR.right.left
          (hsame_trans classifiedHK.right.right classifiedKR.right.right))
    carrier_respects_equiv := by
      intro h k classified _source
      exact classified.right.left
  }
  exact And.intro classifier {
    core := core
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

theorem PdeConservativeStandardBridge_semantic_name_certificate [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      SemanticNameCert
        (fun h : BHist =>
          exists relationBoundary summarizedEndpoint : BHist,
            hsame h endpoint ∧ Cont relation boundary relationBoundary ∧
              Cont (append manifold derivative) relationBoundary summarizedEndpoint)
        (fun h : BHist =>
          exists relationBoundary summarizedEndpoint : BHist,
            hsame h endpoint ∧ Cont relation boundary relationBoundary ∧
              Cont (append manifold derivative) relationBoundary summarizedEndpoint)
        (fun h : BHist =>
          exists relationBoundary summarizedEndpoint : BHist,
            hsame h endpoint ∧ Cont relation boundary relationBoundary ∧
              Cont (append manifold derivative) relationBoundary summarizedEndpoint)
        (fun left right : BHist =>
          (exists relationBoundary summarizedEndpoint : BHist,
            hsame left endpoint ∧ Cont relation boundary relationBoundary ∧
              Cont (append manifold derivative) relationBoundary summarizedEndpoint) ∧
          (exists relationBoundary summarizedEndpoint : BHist,
            hsame right endpoint ∧ Cont relation boundary relationBoundary ∧
              Cont (append manifold derivative) relationBoundary summarizedEndpoint) ∧
          hsame left right) := by
  intro row
  let SourceSpec : BHist -> Prop := fun h : BHist =>
    exists relationBoundary summarizedEndpoint : BHist,
      hsame h endpoint ∧ Cont relation boundary relationBoundary ∧
        Cont (append manifold derivative) relationBoundary summarizedEndpoint
  let ClassifierSpec : BHist -> BHist -> Prop := fun left right : BHist =>
    SourceSpec left ∧ SourceSpec right ∧ hsame left right
  have endpointSource : SourceSpec endpoint :=
    Exists.intro endpoint
      (Exists.intro (append (append manifold derivative) endpoint)
        (And.intro (hsame_refl endpoint)
          (And.intro row.right.right.right.right.left (cont_intro rfl))))
  have core : NameCert SourceSpec ClassifierSpec := {
    carrier_inhabited := Exists.intro endpoint endpointSource
    equiv_refl := by
      intro h source
      exact And.intro source (And.intro source (hsame_refl h))
    equiv_symm := by
      intro h k classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    equiv_trans := by
      intro h k r classifiedHK classifiedKR
      exact And.intro classifiedHK.left
        (And.intro classifiedKR.right.left
          (hsame_trans classifiedHK.right.right classifiedKR.right.right))
    carrier_respects_equiv := by
      intro h k classified _source
      exact classified.right.left
  }
  exact {
    core := core
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

theorem PdeUp_StdBridge [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint relationBoundary summarizedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      Cont relation boundary relationBoundary ->
        Cont (append manifold derivative) relationBoundary summarizedEndpoint ->
          SemanticNameCert
            (fun h : BHist => exists rb se : BHist,
              hsame h endpoint ∧ Cont relation boundary rb ∧
                Cont (append manifold derivative) rb se)
            (fun h : BHist => exists rb se : BHist,
              hsame h endpoint ∧ Cont relation boundary rb ∧
                Cont (append manifold derivative) rb se)
            (fun h : BHist => exists rb se : BHist,
              hsame h endpoint ∧ Cont relation boundary rb ∧
                Cont (append manifold derivative) rb se)
            (fun left right : BHist =>
              (exists lrb lse : BHist,
                hsame left endpoint ∧ Cont relation boundary lrb ∧
                  Cont (append manifold derivative) lrb lse) ∧
              (exists rrb rse : BHist,
                hsame right endpoint ∧ Cont relation boundary rrb ∧
                  Cont (append manifold derivative) rrb rse) ∧
              hsame left right) ∧
            hsame summarizedEndpoint (append (append manifold derivative) endpoint) := by
  intro row relationBoundaryCont summarizedEndpointCont
  have cert :=
    PdeConservativeStandardBridge_semantic_name_certificate
      (manifold := manifold) (derivative := derivative) (relation := relation)
      (boundary := boundary) (endpoint := endpoint) (bundle := bundle) (pkg := pkg) row
  have endpointReadback :=
    PdeConservativeStandardBridge_endpoint_readback
      (manifold := manifold) (derivative := derivative) (relation := relation)
      (boundary := boundary) (endpoint := endpoint) (relationBoundary := relationBoundary)
      (summarizedEndpoint := summarizedEndpoint) (bundle := bundle) (pkg := pkg) row
      relationBoundaryCont summarizedEndpointCont
  exact And.intro cert endpointReadback

theorem PdeCarriedSourceRow_source_scope [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      PkgSig bundle endpoint pkg ∧ hsame relation (append manifold derivative) ∧
        hsame endpoint (append relation boundary) ∧ UnaryHistory endpoint := by
  intro row
  have relationUnary : UnaryHistory relation :=
    unary_cont_closed row.left row.right.left row.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed relationUnary row.right.right.left row.right.right.right.right.left
  exact And.intro row.right.right.right.right.right
    (And.intro row.right.right.right.left
      (And.intro row.right.right.right.right.left endpointUnary))

end BEDC.Derived.PdeUp
