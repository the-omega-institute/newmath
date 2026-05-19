import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_source_target_lock [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName handoff consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg ->
    Cont sourceBoundLeft precision sourceBoundRight ->
    Cont precision targetTriangle handoff ->
    Cont handoff localName consumer ->
    PkgSig bundle sourceBoundRight pkg ->
    PkgSig bundle consumer pkg ->
      SemanticNameCert
          (fun row : BHist =>
            MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
              sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
              targetTriangle transport route provenance localName bundle pkg ∧ hsame row consumer)
          (fun row : BHist =>
            UnaryHistory row ∧
              (hsame row sourceBoundRight ∨ hsame row targetTriangle ∨ hsame row consumer))
          (fun _row : BHist =>
            Cont sourceBoundLeft precision sourceBoundRight ∧
              Cont precision targetTriangle handoff ∧ Cont handoff localName consumer ∧
                PkgSig bundle sourceBoundRight pkg ∧ PkgSig bundle consumer pkg)
          hsame ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier sourceTriangle precisionTriangleHandoff handoffLocalConsumer sourceBoundPkg
    consumerPkg
  have carrierWitness :
      MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
        sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
        targetTriangle transport route provenance localName bundle pkg := carrier
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    _centerUnary, _sourceBoundLeftUnary, _sourceBoundRightUnary, precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localNameUnary, _sourceLeftRoute, _sourceRightRoute,
    _targetTriangleRoute, _localNameRoute, _localNamePkg, _transportTargetTriangle⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed precisionUnary targetTriangleUnary precisionTriangleHandoff
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary localNameUnary handoffLocalConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
              sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
              targetTriangle transport route provenance localName bundle pkg ∧ hsame row consumer)
          (fun row : BHist =>
            UnaryHistory row ∧
              (hsame row sourceBoundRight ∨ hsame row targetTriangle ∨ hsame row consumer))
          (fun _row : BHist =>
            Cont sourceBoundLeft precision sourceBoundRight ∧
              Cont precision targetTriangle handoff ∧ Cont handoff localName consumer ∧
                PkgSig bundle sourceBoundRight pkg ∧ PkgSig bundle consumer pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro consumer
          ⟨carrierWitness, hsame_refl consumer⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          exact
            ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨unary_transport consumerUnary (hsame_symm sourceRow.right),
            Or.inr (Or.inr sourceRow.right)⟩
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨sourceTriangle, precisionTriangleHandoff, handoffLocalConsumer, sourceBoundPkg,
            consumerPkg⟩
    }
  exact ⟨cert, consumerUnary⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
