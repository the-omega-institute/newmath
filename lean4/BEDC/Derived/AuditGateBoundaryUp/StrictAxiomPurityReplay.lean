import BEDC.Derived.AuditGateBoundaryUp

namespace BEDC.Derived.AuditGateBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditGateBoundaryCarrier_strict_axiom_purity_replay [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert sourceConsumer dependencyConsumer strictReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      Cont sourceScan transport sourceConsumer ->
        Cont dependencyReport route dependencyConsumer ->
          Cont sourceConsumer dependencyConsumer strictReplay ->
            PkgSig bundle strictReplay pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution
                    originLedger transport route provenance gap nameCert bundle pkg ∧
                    (hsame row sourceScan ∨ hsame row dependencyReport))
                (fun row : BHist =>
                  UnaryHistory row ∧ (hsame row sourceScan ∨ hsame row dependencyReport))
                (fun row : BHist =>
                  PkgSig bundle strictReplay pkg ∧
                    (hsame row sourceScan ∨ hsame row dependencyReport))
                hsame ∧ UnaryHistory sourceConsumer ∧ UnaryHistory dependencyConsumer ∧
                  UnaryHistory strictReplay ∧ Cont sourceScan transport sourceConsumer ∧
                    Cont dependencyReport route dependencyConsumer ∧
                      Cont sourceConsumer dependencyConsumer strictReplay := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame
  intro carrier sourceRoute dependencyRoute replayRoute replayPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, dependencyUnary, _markerUnary, _originUnary, transportUnary, routeUnary,
    _provenanceUnary, _gapUnary, _nameUnary, _dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, _namePkg⟩ := carrier
  have sourceConsumerUnary : UnaryHistory sourceConsumer :=
    unary_cont_closed sourceUnary transportUnary sourceRoute
  have dependencyConsumerUnary : UnaryHistory dependencyConsumer :=
    unary_cont_closed dependencyUnary routeUnary dependencyRoute
  have strictReplayUnary : UnaryHistory strictReplay :=
    unary_cont_closed sourceConsumerUnary dependencyConsumerUnary replayRoute
  have sourceRow :
      (fun row : BHist =>
        AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
          transport route provenance gap nameCert bundle pkg ∧
          (hsame row sourceScan ∨ hsame row dependencyReport))
        sourceScan := by
    exact And.intro carrierWitness (Or.inl (hsame_refl sourceScan))
  have core :
      NameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧
            (hsame row sourceScan ∨ hsame row dependencyReport))
        hsame := by
    exact {
      carrier_inhabited := Exists.intro sourceScan sourceRow
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
        intro row other same source
        cases source.right with
        | inl sameSource =>
            exact And.intro source.left
              (Or.inl (hsame_trans (hsame_symm same) sameSource))
        | inr sameDependency =>
            exact And.intro source.left
              (Or.inr (hsame_trans (hsame_symm same) sameDependency))
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧
            (hsame row sourceScan ∨ hsame row dependencyReport))
        (fun row : BHist =>
          UnaryHistory row ∧ (hsame row sourceScan ∨ hsame row dependencyReport))
        (fun row : BHist =>
          PkgSig bundle strictReplay pkg ∧
            (hsame row sourceScan ∨ hsame row dependencyReport))
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        cases source.right with
        | inl sameSource =>
            have rowUnary : UnaryHistory row :=
              unary_transport sourceUnary (hsame_symm sameSource)
            exact And.intro rowUnary (Or.inl sameSource)
        | inr sameDependency =>
            have rowUnary : UnaryHistory row :=
              unary_transport dependencyUnary (hsame_symm sameDependency)
            exact And.intro rowUnary (Or.inr sameDependency)
      ledger_sound := by
        intro row source
        exact And.intro replayPkg source.right
    }
  exact
    ⟨cert, sourceConsumerUnary, dependencyConsumerUnary, strictReplayUnary, sourceRoute,
      dependencyRoute, replayRoute⟩

end BEDC.Derived.AuditGateBoundaryUp
