import BEDC.Derived.MetricTriangleUniformEstimateUp.ConsumerHandoff

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_shared_center_triangle_composition
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName handoff consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
        sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
        targetTriangle transport route provenance localName bundle pkg ->
      Cont sourceBoundLeft precision sourceBoundRight ->
        Cont precision targetTriangle handoff ->
          Cont handoff localName consumer ->
            PkgSig bundle sourceBoundRight pkg ->
              PkgSig bundle consumer pkg ->
                UnaryHistory center ∧ UnaryHistory sourceBoundLeft ∧
                  UnaryHistory sourceBoundRight ∧ UnaryHistory targetTriangle ∧
                    UnaryHistory consumer ∧ Cont left center sourceBoundLeft ∧
                      Cont right center sourceBoundRight ∧
                        Cont sourceBoundLeft precision sourceBoundRight ∧
                          Cont targetBoundLeft targetBoundRight targetTriangle ∧
                            Cont precision targetTriangle handoff ∧
                              Cont handoff localName consumer ∧ PkgSig bundle localName pkg ∧
                                PkgSig bundle sourceBoundRight pkg ∧
                                  PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  intro carrier sourceTriangle precisionTriangleHandoff handoffLocalConsumer sourceBoundPkg
    consumerPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    centerUnary, sourceBoundLeftUnary, sourceBoundRightUnary, precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localNameUnary, leftCenterSourceBound,
    rightCenterSourceBound, targetTriangleRoute, _routeProvenanceLocalName, localNamePkg,
    _transportTargetTriangle⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed precisionUnary targetTriangleUnary precisionTriangleHandoff
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary localNameUnary handoffLocalConsumer
  exact
    ⟨centerUnary, sourceBoundLeftUnary, sourceBoundRightUnary, targetTriangleUnary,
      consumerUnary, leftCenterSourceBound, rightCenterSourceBound, sourceTriangle,
      targetTriangleRoute, precisionTriangleHandoff, handoffLocalConsumer, localNamePkg,
      sourceBoundPkg, consumerPkg⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
