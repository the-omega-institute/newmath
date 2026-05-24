import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditGateBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive AuditGateBoundaryUp : Type where
  | mk
      (sourceScan dependencyReport targetAudit originLedger transport continuation provenance gap name :
        BHist) :
      AuditGateBoundaryUp

def AuditGateBoundaryCarrier [AskSetup] [PackageSetup]
    (sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceScan ∧ UnaryHistory dependencyReport ∧ UnaryHistory markerResolution ∧
    UnaryHistory originLedger ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory gap ∧ UnaryHistory nameCert ∧
        hsame dependencyReport gap ∧ hsame nameCert gap ∧
          Cont sourceScan dependencyReport markerResolution ∧
            Cont markerResolution originLedger transport ∧ Cont transport route provenance ∧
              Cont provenance gap nameCert ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle nameCert pkg

theorem AuditGateBoundaryCarrier_axiom_purity_soundness [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row dependencyReport)
        (fun row : BHist => hsame row gap ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row dependencyReport)
        hsame := by
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, dependencyUnary, _markerUnary, _originUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _gapUnary, _nameUnary, dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, provenancePkg, _namePkg⟩ := carrier
  have sourceDependency :
      (fun row : BHist =>
        AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
          transport route provenance gap nameCert bundle pkg ∧ hsame row dependencyReport)
        dependencyReport := by
    exact And.intro carrierWitness (hsame_refl dependencyReport)
  have core :
      NameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row dependencyReport)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro dependencyReport sourceDependency
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameRowDependency : hsame row dependencyReport := sourceRow.right
        have sameOtherDependency : hsame other dependencyReport :=
          hsame_trans (hsame_symm same) sameRowDependency
        exact And.intro sourceRow.left sameOtherDependency
    }
  exact {
    core := core
    pattern_sound := by
      intro row sourceRow
      have rowGap : hsame row gap :=
        hsame_trans sourceRow.right dependencyGap
      have rowUnary : UnaryHistory row :=
        unary_transport dependencyUnary (hsame_symm sourceRow.right)
      exact And.intro rowGap rowUnary
    ledger_sound := by
      intro row sourceRow
      exact And.intro provenancePkg sourceRow.right
  }

theorem AuditGateBoundaryCarrier_paper_lean_drift_exactness [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert markerConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      Cont markerResolution originLedger markerConsumer ->
        PkgSig bundle markerConsumer pkg ->
          SemanticNameCert
            (fun row : BHist =>
              AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution
                originLedger transport route provenance gap nameCert bundle pkg ∧
                hsame row markerResolution)
            (fun row : BHist => hsame row markerResolution ∧ UnaryHistory row)
            (fun row : BHist => PkgSig bundle markerConsumer pkg ∧ hsame row markerResolution)
            hsame ∧ UnaryHistory markerResolution ∧
              Cont markerResolution originLedger markerConsumer := by
  intro carrier markerRoute markerPkg
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, _dependencyUnary, markerUnary, _originUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _gapUnary, _nameUnary, _dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, _namePkg⟩ := carrier
  have sourceMarker :
      (fun row : BHist =>
        AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
          transport route provenance gap nameCert bundle pkg ∧ hsame row markerResolution)
        markerResolution := by
    exact And.intro carrierWitness (hsame_refl markerResolution)
  have core :
      NameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row markerResolution)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro markerResolution sourceMarker
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameRowMarker : hsame row markerResolution := sourceRow.right
        have sameOtherMarker : hsame other markerResolution :=
          hsame_trans (hsame_symm same) sameRowMarker
        exact And.intro sourceRow.left sameOtherMarker
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row markerResolution)
        (fun row : BHist => hsame row markerResolution ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle markerConsumer pkg ∧ hsame row markerResolution)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row sourceRow
        have rowUnary : UnaryHistory row :=
          unary_transport markerUnary (hsame_symm sourceRow.right)
        exact And.intro sourceRow.right rowUnary
      ledger_sound := by
        intro row sourceRow
        exact And.intro markerPkg sourceRow.right
    }
  exact ⟨cert, markerUnary, markerRoute⟩

theorem AuditGateBoundaryCarrier_source_token_refusal [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert sourceConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      Cont sourceScan transport sourceConsumer ->
        PkgSig bundle sourceConsumer pkg ->
          UnaryHistory sourceScan ∧ UnaryHistory transport ∧ UnaryHistory sourceConsumer ∧
            Cont sourceScan transport sourceConsumer ∧ PkgSig bundle sourceConsumer pkg := by
  intro carrier sourceRoute sourcePkg
  obtain ⟨sourceUnary, _dependencyUnary, _markerUnary, _originUnary, transportUnary,
    _routeUnary, _provenanceUnary, _gapUnary, _nameUnary, _dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, _namePkg⟩ := carrier
  have consumerUnary : UnaryHistory sourceConsumer :=
    unary_cont_closed sourceUnary transportUnary sourceRoute
  exact ⟨sourceUnary, transportUnary, consumerUnary, sourceRoute, sourcePkg⟩

theorem AuditGateBoundaryCarrier_drift_row_transport [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert transportedMarker markerConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      hsame markerResolution transportedMarker ->
        Cont transportedMarker route markerConsumer ->
          PkgSig bundle markerConsumer pkg ->
            SemanticNameCert
              (fun row : BHist =>
                AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution
                  originLedger transport route provenance gap nameCert bundle pkg ∧
                  hsame row transportedMarker)
              (fun row : BHist => hsame row transportedMarker ∧ UnaryHistory row)
              (fun row : BHist => PkgSig bundle markerConsumer pkg ∧
                hsame row transportedMarker)
              hsame ∧ UnaryHistory transportedMarker ∧ UnaryHistory markerConsumer ∧
                Cont transportedMarker route markerConsumer := by
  intro carrier markerTransport markerRoute markerPkg
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, _dependencyUnary, markerUnary, _originUnary, _transportUnary,
    routeUnary, _provenanceUnary, _gapUnary, _nameUnary, _dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, _namePkg⟩ := carrier
  have transportedUnary : UnaryHistory transportedMarker :=
    unary_transport markerUnary markerTransport
  have markerConsumerUnary : UnaryHistory markerConsumer :=
    unary_cont_closed transportedUnary routeUnary markerRoute
  have sourceTransported :
      (fun row : BHist =>
        AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
          transport route provenance gap nameCert bundle pkg ∧ hsame row transportedMarker)
        transportedMarker := by
    exact And.intro carrierWitness (hsame_refl transportedMarker)
  have core :
      NameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row transportedMarker)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro transportedMarker sourceTransported
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameRowTransported : hsame row transportedMarker := sourceRow.right
        have sameOtherTransported : hsame other transportedMarker :=
          hsame_trans (hsame_symm same) sameRowTransported
        exact And.intro sourceRow.left sameOtherTransported
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row transportedMarker)
        (fun row : BHist => hsame row transportedMarker ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle markerConsumer pkg ∧ hsame row transportedMarker)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row sourceRow
        have rowUnary : UnaryHistory row :=
          unary_transport transportedUnary (hsame_symm sourceRow.right)
        exact And.intro sourceRow.right rowUnary
      ledger_sound := by
        intro row sourceRow
        exact And.intro markerPkg sourceRow.right
    }
  exact ⟨cert, transportedUnary, markerConsumerUnary, markerRoute⟩

theorem AuditGateBoundaryCarrier_replay_ledger [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert sourceConsumer dependencyConsumer markerConsumer originConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      Cont sourceScan transport sourceConsumer ->
        Cont dependencyReport route dependencyConsumer ->
          Cont markerResolution originLedger markerConsumer ->
            Cont originLedger transport originConsumer ->
              PkgSig bundle sourceConsumer pkg ->
                PkgSig bundle dependencyConsumer pkg ->
                  PkgSig bundle markerConsumer pkg ->
                    PkgSig bundle originConsumer pkg ->
                      UnaryHistory sourceConsumer ∧ UnaryHistory dependencyConsumer ∧
                        UnaryHistory markerConsumer ∧ UnaryHistory originConsumer ∧
                          Cont sourceScan transport sourceConsumer ∧
                            Cont dependencyReport route dependencyConsumer ∧
                              Cont markerResolution originLedger markerConsumer ∧
                                Cont originLedger transport originConsumer := by
  intro carrier sourceRoute dependencyRoute markerRoute originRoute _sourcePkg _dependencyPkg
    _markerPkg _originPkg
  obtain ⟨sourceUnary, dependencyUnary, markerUnary, originUnary, transportUnary, routeUnary,
    _provenanceUnary, _gapUnary, _nameUnary, _dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, _namePkg⟩ := carrier
  have sourceConsumerUnary : UnaryHistory sourceConsumer :=
    unary_cont_closed sourceUnary transportUnary sourceRoute
  have dependencyConsumerUnary : UnaryHistory dependencyConsumer :=
    unary_cont_closed dependencyUnary routeUnary dependencyRoute
  have markerConsumerUnary : UnaryHistory markerConsumer :=
    unary_cont_closed markerUnary originUnary markerRoute
  have originConsumerUnary : UnaryHistory originConsumer :=
    unary_cont_closed originUnary transportUnary originRoute
  exact
    ⟨sourceConsumerUnary, dependencyConsumerUnary, markerConsumerUnary, originConsumerUnary,
      sourceRoute, dependencyRoute, markerRoute, originRoute⟩

theorem AuditGateBoundaryCarrier_origin_import_replay_exactness [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert originConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      Cont originLedger transport originConsumer ->
        PkgSig bundle originConsumer pkg ->
          SemanticNameCert
            (fun row : BHist =>
              AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution
                originLedger transport route provenance gap nameCert bundle pkg ∧
                hsame row originLedger)
            (fun row : BHist => hsame row originLedger ∧ UnaryHistory row)
            (fun row : BHist => PkgSig bundle originConsumer pkg ∧ hsame row originLedger)
            hsame ∧ UnaryHistory originLedger ∧ UnaryHistory transport ∧
              UnaryHistory originConsumer ∧ Cont originLedger transport originConsumer ∧
                PkgSig bundle originConsumer pkg := by
  intro carrier originRoute originPkg
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, _dependencyUnary, _markerUnary, originUnary, transportUnary,
    _routeUnary, _provenanceUnary, _gapUnary, _nameUnary, _dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, _namePkg⟩ := carrier
  have sourceOrigin :
      (fun row : BHist =>
        AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
          transport route provenance gap nameCert bundle pkg ∧ hsame row originLedger)
        originLedger := by
    exact And.intro carrierWitness (hsame_refl originLedger)
  have core :
      NameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row originLedger)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro originLedger sourceOrigin
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameRowOrigin : hsame row originLedger := sourceRow.right
        have sameOtherOrigin : hsame other originLedger :=
          hsame_trans (hsame_symm same) sameRowOrigin
        exact And.intro sourceRow.left sameOtherOrigin
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row originLedger)
        (fun row : BHist => hsame row originLedger ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle originConsumer pkg ∧ hsame row originLedger)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row sourceRow
        have rowUnary : UnaryHistory row :=
          unary_transport originUnary (hsame_symm sourceRow.right)
        exact And.intro sourceRow.right rowUnary
      ledger_sound := by
        intro row sourceRow
        exact And.intro originPkg sourceRow.right
    }
  have originConsumerUnary : UnaryHistory originConsumer :=
    unary_cont_closed originUnary transportUnary originRoute
  exact ⟨cert, originUnary, transportUnary, originConsumerUnary, originRoute, originPkg⟩

theorem AuditGateBoundaryCarrier_dependency_forbidden_set [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert dependencyConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      Cont dependencyReport route dependencyConsumer ->
        PkgSig bundle dependencyConsumer pkg ->
          SemanticNameCert
            (fun row : BHist =>
              AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution
                originLedger transport route provenance gap nameCert bundle pkg ∧
                hsame row dependencyReport)
            (fun row : BHist =>
              hsame row gap ∧ UnaryHistory row ∧
                Cont dependencyReport route dependencyConsumer)
            (fun row : BHist => PkgSig bundle dependencyConsumer pkg ∧
              hsame row dependencyReport)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro carrier dependencyRoute dependencyPkg
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, dependencyUnary, _markerUnary, _originUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _gapUnary, _nameUnary, dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, _namePkg⟩ := carrier
  have sourceDependency :
      (fun row : BHist =>
        AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
          transport route provenance gap nameCert bundle pkg ∧ hsame row dependencyReport)
        dependencyReport := by
    exact And.intro carrierWitness (hsame_refl dependencyReport)
  have core :
      NameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row dependencyReport)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro dependencyReport sourceDependency
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameRowDependency : hsame row dependencyReport := sourceRow.right
        have sameOtherDependency : hsame other dependencyReport :=
          hsame_trans (hsame_symm same) sameRowDependency
        exact And.intro sourceRow.left sameOtherDependency
    }
  exact {
    core := core
    pattern_sound := by
      intro row sourceRow
      have rowGap : hsame row gap :=
        hsame_trans sourceRow.right dependencyGap
      have rowUnary : UnaryHistory row :=
        unary_transport dependencyUnary (hsame_symm sourceRow.right)
      exact ⟨rowGap, rowUnary, dependencyRoute⟩
    ledger_sound := by
      intro row sourceRow
      exact And.intro dependencyPkg sourceRow.right
  }

theorem AuditGateBoundaryCarrier_marker_resolution_nonescape [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert markerConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      Cont markerResolution route markerConsumer ->
        PkgSig bundle markerConsumer pkg ->
          SemanticNameCert
            (fun row : BHist =>
              AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution
                originLedger transport route provenance gap nameCert bundle pkg ∧
                hsame row markerResolution)
            (fun row : BHist =>
              hsame row markerResolution ∧ UnaryHistory row ∧
                Cont markerResolution route markerConsumer)
            (fun row : BHist => PkgSig bundle markerConsumer pkg ∧ hsame row markerResolution)
            hsame ∧ UnaryHistory markerResolution ∧ UnaryHistory route ∧
              UnaryHistory markerConsumer ∧ Cont markerResolution route markerConsumer := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame
  intro carrier markerRoute markerPkg
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, _dependencyUnary, markerUnary, _originUnary, _transportUnary,
    routeUnary, _provenanceUnary, _gapUnary, _nameUnary, _dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, _namePkg⟩ := carrier
  have markerConsumerUnary : UnaryHistory markerConsumer :=
    unary_cont_closed markerUnary routeUnary markerRoute
  have sourceMarker :
      (fun row : BHist =>
        AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
          transport route provenance gap nameCert bundle pkg ∧ hsame row markerResolution)
        markerResolution := by
    exact And.intro carrierWitness (hsame_refl markerResolution)
  have core :
      NameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row markerResolution)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro markerResolution sourceMarker
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameRowMarker : hsame row markerResolution := sourceRow.right
        have sameOtherMarker : hsame other markerResolution :=
          hsame_trans (hsame_symm same) sameRowMarker
        exact And.intro sourceRow.left sameOtherMarker
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row markerResolution)
        (fun row : BHist =>
          hsame row markerResolution ∧ UnaryHistory row ∧
            Cont markerResolution route markerConsumer)
        (fun row : BHist => PkgSig bundle markerConsumer pkg ∧ hsame row markerResolution)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row sourceRow
        have rowUnary : UnaryHistory row :=
          unary_transport markerUnary (hsame_symm sourceRow.right)
        exact ⟨sourceRow.right, rowUnary, markerRoute⟩
      ledger_sound := by
        intro row sourceRow
        exact And.intro markerPkg sourceRow.right
    }
  exact ⟨cert, markerUnary, routeUnary, markerConsumerUnary, markerRoute⟩

theorem AuditGateBoundaryTasteGate_single_carrier_alignment :
    (AuditGateBoundaryUp.mk BHist.Empty (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ≠
      (AuditGateBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases h

end BEDC.Derived.AuditGateBoundaryUp
