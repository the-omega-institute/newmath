import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_uniformmodulus_readiness
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName handoff consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
      targetTriangle transport route provenance localName bundle pkg ->
    Cont precision targetTriangle handoff ->
    Cont handoff localName consumer ->
    PkgSig bundle consumer pkg ->
      SemanticNameCert
        (fun row : BHist =>
          MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
            sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
            targetTriangle transport route provenance localName bundle pkg ∧ hsame row consumer)
        (fun row : BHist =>
          UnaryHistory row ∧
            (hsame row precision ∨ hsame row targetTriangle ∨ hsame row handoff ∨
              hsame row consumer))
        (fun _row : BHist =>
          Cont precision targetTriangle handoff ∧ Cont handoff localName consumer ∧
            PkgSig bundle localName pkg ∧ PkgSig bundle consumer pkg)
        hsame ∧ UnaryHistory handoff ∧ UnaryHistory consumer ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier precisionTargetHandoff handoffLocalConsumer consumerPkg
  have carrierWitness :
      MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
        sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
        targetTriangle transport route provenance localName bundle pkg := carrier
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    _centerUnary, _sourceBoundLeftUnary, _sourceBoundRightUnary, precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRow, _routeProvenanceLocalName, localNamePkg,
    _transportTargetTriangle⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed precisionUnary targetTriangleUnary precisionTargetHandoff
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
            (hsame row precision ∨ hsame row targetTriangle ∨ hsame row handoff ∨
              hsame row consumer))
        (fun _row : BHist =>
          Cont precision targetTriangle handoff ∧ Cont handoff localName consumer ∧
            PkgSig bundle localName pkg ∧ PkgSig bundle consumer pkg)
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
            Or.inr (Or.inr (Or.inr sourceRow.right))⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨precisionTargetHandoff, handoffLocalConsumer, localNamePkg, consumerPkg⟩
    }
  exact ⟨cert, handoffUnary, consumerUnary, consumerPkg⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
