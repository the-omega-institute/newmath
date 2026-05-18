import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_uniform_modulus_export [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName centerPrecision sourceExtraction exportRow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg ->
      Cont center precision centerPrecision ->
        Cont centerPrecision sourceBoundLeft sourceExtraction ->
          Cont sourceExtraction sourceBoundRight route ->
            Cont sourceExtraction targetTriangle exportRow ->
              Cont exportRow localName consumer ->
                PkgSig bundle exportRow pkg ->
                  PkgSig bundle consumer pkg ->
                    UnaryHistory center ∧ UnaryHistory precision ∧
                      UnaryHistory sourceBoundLeft ∧ UnaryHistory sourceBoundRight ∧
                        UnaryHistory targetBoundLeft ∧ UnaryHistory targetBoundRight ∧
                          UnaryHistory targetTriangle ∧ UnaryHistory sourceExtraction ∧
                            UnaryHistory exportRow ∧ UnaryHistory consumer ∧
                              Cont targetBoundLeft targetBoundRight targetTriangle ∧
                                Cont sourceExtraction targetTriangle exportRow ∧
                                  Cont exportRow localName consumer ∧
                                    hsame transport targetTriangle ∧
                                      PkgSig bundle localName pkg ∧
                                        PkgSig bundle exportRow pkg ∧
                                          PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame UnaryHistory
  intro carrier centerPrecisionRoute centerSourceExtraction _sourceExtractionRoute
    sourceTargetExport exportLocalConsumer exportPkg consumerPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    centerUnary, sourceBoundLeftUnary, sourceBoundRightUnary, precisionUnary,
    targetBoundLeftUnary, targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, targetTriangleRoute, _routeProvenanceLocalName,
    localNamePkg, transportTargetTriangle⟩ := carrier
  have centerPrecisionUnary : UnaryHistory centerPrecision :=
    unary_cont_closed centerUnary precisionUnary centerPrecisionRoute
  have sourceExtractionUnary : UnaryHistory sourceExtraction :=
    unary_cont_closed centerPrecisionUnary sourceBoundLeftUnary centerSourceExtraction
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed sourceExtractionUnary targetTriangleUnary sourceTargetExport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed exportUnary localNameUnary exportLocalConsumer
  exact
    ⟨centerUnary, precisionUnary, sourceBoundLeftUnary, sourceBoundRightUnary,
      targetBoundLeftUnary, targetBoundRightUnary, targetTriangleUnary,
      sourceExtractionUnary, exportUnary, consumerUnary, targetTriangleRoute,
      sourceTargetExport, exportLocalConsumer, transportTargetTriangle, localNamePkg,
      exportPkg, consumerPkg⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
