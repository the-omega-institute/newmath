import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_two_point_target_boundary
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName targetRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
        sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
        targetTriangle transport route provenance localName bundle pkg ->
      Cont targetBoundLeft targetBoundRight targetTriangle ->
        Cont targetTriangle localName targetRead ->
          Cont targetRead precision consumer ->
            PkgSig bundle consumer pkg ->
              UnaryHistory targetBoundLeft /\ UnaryHistory targetBoundRight /\
                UnaryHistory targetTriangle /\ UnaryHistory targetRead /\ UnaryHistory consumer /\
                  Cont targetBoundLeft targetBoundRight targetTriangle /\
                    Cont targetTriangle localName targetRead /\
                      Cont targetRead precision consumer /\ hsame transport targetTriangle /\
                        PkgSig bundle localName pkg /\ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig UnaryHistory
  intro carrier targetTriangleRoute targetTriangleLocalRead targetReadPrecisionConsumer
    consumerPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    _centerUnary, _sourceBoundLeftUnary, _sourceBoundRightUnary, precisionUnary,
    targetBoundLeftUnary, targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, _carrierTargetTriangleRoute, _routeProvenanceLocalName,
    localNamePkg, transportTargetTriangle⟩ := carrier
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed targetTriangleUnary localNameUnary targetTriangleLocalRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed targetReadUnary precisionUnary targetReadPrecisionConsumer
  exact
    ⟨targetBoundLeftUnary, targetBoundRightUnary, targetTriangleUnary, targetReadUnary,
      consumerUnary, targetTriangleRoute, targetTriangleLocalRead, targetReadPrecisionConsumer,
      transportTargetTriangle, localNamePkg, consumerPkg⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
