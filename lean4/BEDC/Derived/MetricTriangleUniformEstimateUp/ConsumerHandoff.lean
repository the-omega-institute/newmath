import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_consumer_handoff
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
        sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
        targetTriangle transport route provenance localName bundle pkg ->
      Cont precision targetTriangle handoff ->
        PkgSig bundle handoff pkg ->
          UnaryHistory precision ∧ UnaryHistory sourceBoundLeft ∧
            UnaryHistory sourceBoundRight ∧ UnaryHistory targetBoundLeft ∧
              UnaryHistory targetBoundRight ∧ UnaryHistory targetTriangle ∧
                UnaryHistory handoff ∧ Cont left center sourceBoundLeft ∧
                  Cont right center sourceBoundRight ∧
                    Cont targetBoundLeft targetBoundRight targetTriangle ∧
                      Cont precision targetTriangle handoff ∧ hsame transport targetTriangle ∧
                        PkgSig bundle localName pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier precisionTriangleHandoff handoffPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    _centerUnary, sourceBoundLeftUnary, sourceBoundRightUnary, precisionUnary,
    targetBoundLeftUnary, targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, leftCenterSourceBound,
    rightCenterSourceBound, targetTriangleRow, _routeProvenanceLocalName, localNamePkg,
    transportTargetTriangle⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed precisionUnary targetTriangleUnary precisionTriangleHandoff
  exact
    ⟨precisionUnary, sourceBoundLeftUnary, sourceBoundRightUnary, targetBoundLeftUnary,
      targetBoundRightUnary, targetTriangleUnary, handoffUnary, leftCenterSourceBound,
      rightCenterSourceBound, targetTriangleRow, precisionTriangleHandoff,
      transportTargetTriangle, localNamePkg, handoffPkg⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
