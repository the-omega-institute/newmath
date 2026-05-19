import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_namecert_scope [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
        sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
        targetTriangle transport route provenance localName bundle pkg ->
      Cont route localName consumer ->
        PkgSig bundle consumer pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row sourceMetric ∨ hsame row targetMetric ∨ hsame row targetTriangle ∨
                hsame row consumer)
            (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier routeLocalConsumer consumerPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    _centerUnary, _sourceBoundLeftUnary, _sourceBoundRightUnary, _precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, _targetTriangleUnary, _transportUnary,
    routeUnary, _provenanceUnary, localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRoute, _routeProvenanceLocalName, _localNamePkg,
    _transportTargetTriangle⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary localNameUnary routeLocalConsumer
  exact {
    core := {
      carrier_inhabited := Exists.intro consumer
        ⟨hsame_refl consumer, consumerUnary⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }

end BEDC.Derived.MetricTriangleUniformEstimateUp
