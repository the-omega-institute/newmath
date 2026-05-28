import BEDC.Derived.AuditGateBoundaryUp

namespace BEDC.Derived.AuditGateBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditGateBoundaryCarrier_kernel_query_scope [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert sourceConsumer dependencyConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      Cont sourceScan transport sourceConsumer ->
        Cont dependencyReport route dependencyConsumer ->
          PkgSig bundle sourceConsumer pkg ->
            PkgSig bundle dependencyConsumer pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row sourceConsumer ∨ hsame row dependencyConsumer) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row sourceScan ∨ hsame row dependencyReport ∨
                      hsame row sourceConsumer ∨ hsame row dependencyConsumer)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle sourceConsumer pkg ∧
                      PkgSig bundle dependencyConsumer pkg)
                  hsame ∧
                UnaryHistory sourceConsumer ∧ UnaryHistory dependencyConsumer ∧
                  Cont sourceScan transport sourceConsumer ∧
                    Cont dependencyReport route dependencyConsumer := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier sourceRoute dependencyRoute sourcePkg dependencyPkg
  obtain ⟨sourceUnary, dependencyUnary, _markerUnary, _originUnary, transportUnary,
    routeUnary, _provenanceUnary, _gapUnary, _nameUnary, _dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, _namePkg⟩ := carrier
  have sourceConsumerUnary : UnaryHistory sourceConsumer :=
    unary_cont_closed sourceUnary transportUnary sourceRoute
  have dependencyConsumerUnary : UnaryHistory dependencyConsumer :=
    unary_cont_closed dependencyUnary routeUnary dependencyRoute
  have sourceConsumerSource :
      (fun row : BHist =>
        (hsame row sourceConsumer ∨ hsame row dependencyConsumer) ∧ UnaryHistory row)
        sourceConsumer := by
    exact ⟨Or.inl (hsame_refl sourceConsumer), sourceConsumerUnary⟩
  have core :
      NameCert
        (fun row : BHist =>
          (hsame row sourceConsumer ∨ hsame row dependencyConsumer) ∧ UnaryHistory row)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro sourceConsumer sourceConsumerSource
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
        have otherChoice : hsame other sourceConsumer ∨ hsame other dependencyConsumer := by
          cases sourceRow.left with
          | inl sameSource =>
              exact Or.inl (hsame_trans (hsame_symm same) sameSource)
          | inr sameDependency =>
              exact Or.inr (hsame_trans (hsame_symm same) sameDependency)
        have otherUnary : UnaryHistory other :=
          unary_transport sourceRow.right same
        exact ⟨otherChoice, otherUnary⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sourceConsumer ∨ hsame row dependencyConsumer) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceScan ∨ hsame row dependencyReport ∨
              hsame row sourceConsumer ∨ hsame row dependencyConsumer)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sourceConsumer pkg ∧
              PkgSig bundle dependencyConsumer pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row sourceRow
        cases sourceRow.left with
        | inl sameSource =>
            exact Or.inr (Or.inr (Or.inl sameSource))
        | inr sameDependency =>
            exact Or.inr (Or.inr (Or.inr sameDependency))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, sourcePkg, dependencyPkg⟩
    }
  exact
    ⟨cert, sourceConsumerUnary, dependencyConsumerUnary, sourceRoute, dependencyRoute⟩

end BEDC.Derived.AuditGateBoundaryUp
