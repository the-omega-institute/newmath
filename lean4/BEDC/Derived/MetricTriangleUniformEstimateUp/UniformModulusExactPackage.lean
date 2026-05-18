import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_uniform_modulus_exact_package
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName centerPrecision sourceExtraction exportRow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg ->
    Cont center precision centerPrecision ->
    Cont centerPrecision sourceBoundLeft sourceExtraction ->
    Cont sourceExtraction targetTriangle exportRow ->
    Cont exportRow localName consumer ->
    PkgSig bundle exportRow pkg ->
    PkgSig bundle consumer pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row consumer ∧ Cont sourceExtraction targetTriangle exportRow ∧
            Cont exportRow localName consumer)
        (fun row : BHist =>
          hsame row consumer ∧ PkgSig bundle exportRow pkg ∧ PkgSig bundle consumer pkg)
        hsame ∧ UnaryHistory sourceExtraction ∧ UnaryHistory exportRow ∧
          UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier centerPrecisionRoute sourceExtractionRoute exportRoute consumerRoute
    exportPkg consumerPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    centerUnary, sourceBoundLeftUnary, _sourceBoundRightUnary, precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRoute, _routeProvenanceLocalName,
    _localNamePkg, _transportTargetTriangle⟩ := carrier
  have centerPrecisionUnary : UnaryHistory centerPrecision :=
    unary_cont_closed centerUnary precisionUnary centerPrecisionRoute
  have sourceExtractionUnary : UnaryHistory sourceExtraction :=
    unary_cont_closed centerPrecisionUnary sourceBoundLeftUnary sourceExtractionRoute
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed sourceExtractionUnary targetTriangleUnary exportRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed exportUnary localNameUnary consumerRoute
  have sourceConsumer :
      (fun row : BHist => hsame row consumer ∧ UnaryHistory row) consumer := by
    exact ⟨hsame_refl consumer, consumerUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row consumer ∧ Cont sourceExtraction targetTriangle exportRow ∧
            Cont exportRow localName consumer)
        (fun row : BHist =>
          hsame row consumer ∧ PkgSig bundle exportRow pkg ∧ PkgSig bundle consumer pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro consumer sourceConsumer
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
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, exportRoute, consumerRoute⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, exportPkg, consumerPkg⟩
    }
  exact ⟨cert, sourceExtractionUnary, exportUnary, consumerUnary⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
