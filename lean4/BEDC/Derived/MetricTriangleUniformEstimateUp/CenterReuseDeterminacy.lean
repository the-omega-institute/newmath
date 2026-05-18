import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_center_reuse_determinacy
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName handoff consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg ->
      Cont precision targetTriangle handoff ->
      Cont handoff localName consumer ->
      PkgSig bundle consumer pkg ->
        UnaryHistory center ∧ UnaryHistory targetBoundLeft ∧ UnaryHistory targetBoundRight ∧
          UnaryHistory targetTriangle ∧ UnaryHistory handoff ∧ UnaryHistory consumer ∧
            Cont left center sourceBoundLeft ∧ Cont right center sourceBoundRight ∧
              Cont targetBoundLeft targetBoundRight targetTriangle ∧
                Cont precision targetTriangle handoff ∧ Cont handoff localName consumer ∧
                  hsame transport targetTriangle ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier precisionTriangleHandoff handoffLocalConsumer consumerPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    centerUnary, _sourceBoundLeftUnary, _sourceBoundRightUnary, precisionUnary,
    targetBoundLeftUnary, targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localNameUnary, leftCenterSourceBound,
    rightCenterSourceBound, targetTriangleRow, _routeProvenanceLocalName, localNamePkg,
    transportTargetTriangle⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed precisionUnary targetTriangleUnary precisionTriangleHandoff
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary localNameUnary handoffLocalConsumer
  exact
    ⟨centerUnary, targetBoundLeftUnary, targetBoundRightUnary, targetTriangleUnary,
      handoffUnary, consumerUnary, leftCenterSourceBound, rightCenterSourceBound,
      targetTriangleRow, precisionTriangleHandoff, handoffLocalConsumer,
      transportTargetTriangle, localNamePkg, consumerPkg⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
