import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_compact_net_triangle_extraction
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName centerPrecision sourceExtraction : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg ->
      Cont center precision centerPrecision ->
        Cont centerPrecision sourceBoundLeft sourceExtraction ->
          Cont sourceExtraction sourceBoundRight route ->
            PkgSig bundle sourceExtraction pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left
                    right center sourceBoundLeft sourceBoundRight precision targetBoundLeft
                    targetBoundRight targetTriangle transport route provenance localName
                    bundle pkg ∧ hsame row sourceExtraction)
                (fun row : BHist =>
                  UnaryHistory row ∧ (hsame row center ∨ hsame row precision ∨
                    hsame row sourceBoundLeft ∨ hsame row sourceBoundRight ∨
                      hsame row sourceExtraction))
                (fun _row : BHist =>
                  Cont center precision centerPrecision ∧
                    Cont centerPrecision sourceBoundLeft sourceExtraction ∧
                      Cont sourceExtraction sourceBoundRight route ∧
                        PkgSig bundle localName pkg ∧
                          PkgSig bundle sourceExtraction pkg)
                hsame ∧ UnaryHistory sourceExtraction := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier centerPrecisionRoute centerSourceExtraction sourceExtractionRoute
    sourceExtractionPkg
  have carrierWitness :
      MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
        sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
        targetTriangle transport route provenance localName bundle pkg := carrier
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    centerUnary, sourceBoundLeftUnary, _sourceBoundRightUnary, precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, _targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRoute, _routeProvenanceLocalName,
    localNamePkg, _transportTargetTriangle⟩ := carrier
  have centerPrecisionUnary : UnaryHistory centerPrecision :=
    unary_cont_closed centerUnary precisionUnary centerPrecisionRoute
  have sourceExtractionUnary : UnaryHistory sourceExtraction :=
    unary_cont_closed centerPrecisionUnary sourceBoundLeftUnary centerSourceExtraction
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right
            center sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
            targetTriangle transport route provenance localName bundle pkg ∧
              hsame row sourceExtraction)
        (fun row : BHist =>
          UnaryHistory row ∧ (hsame row center ∨ hsame row precision ∨
            hsame row sourceBoundLeft ∨ hsame row sourceBoundRight ∨
              hsame row sourceExtraction))
        (fun _row : BHist =>
          Cont center precision centerPrecision ∧
            Cont centerPrecision sourceBoundLeft sourceExtraction ∧
              Cont sourceExtraction sourceBoundRight route ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle sourceExtraction pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sourceExtraction
          ⟨carrierWitness, hsame_refl sourceExtraction⟩
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
          ⟨unary_transport sourceExtractionUnary (hsame_symm sourceRow.right),
            Or.inr (Or.inr (Or.inr (Or.inr sourceRow.right)))⟩
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨centerPrecisionRoute, centerSourceExtraction, sourceExtractionRoute,
            localNamePkg, sourceExtractionPkg⟩
    }
  exact ⟨cert, sourceExtractionUnary⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
