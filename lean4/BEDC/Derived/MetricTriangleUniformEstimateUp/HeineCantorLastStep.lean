import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_heine_cantor_last_step [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName handoff consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg ->
      Cont left center sourceBoundLeft ->
        Cont right center sourceBoundRight ->
          Cont targetBoundLeft targetBoundRight targetTriangle ->
            Cont precision targetTriangle handoff ->
              Cont handoff localName consumer ->
                PkgSig bundle consumer pkg ->
                  UnaryHistory center ∧ UnaryHistory sourceBoundLeft ∧
                    UnaryHistory sourceBoundRight ∧ UnaryHistory targetBoundLeft ∧
                      UnaryHistory targetBoundRight ∧ UnaryHistory targetTriangle ∧
                        UnaryHistory consumer ∧ Cont left center sourceBoundLeft ∧
                          Cont right center sourceBoundRight ∧
                            Cont targetBoundLeft targetBoundRight targetTriangle ∧
                              Cont precision targetTriangle handoff ∧
                                Cont handoff localName consumer ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier leftCenterSourceBound rightCenterSourceBound targetTriangleRoute
    precisionTriangleHandoff handoffLocalConsumer consumerPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, leftUnary, rightUnary,
    centerUnary, _sourceBoundLeftUnary, _sourceBoundRightUnary, precisionUnary,
    targetBoundLeftUnary, targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localNameUnary, _carrierLeftCenterSourceBound,
    _carrierRightCenterSourceBound, _carrierTargetTriangleRoute, _routeProvenanceLocalName,
    _localNamePkg, _transportTargetTriangle⟩ := carrier
  have sourceBoundLeftUnary : UnaryHistory sourceBoundLeft :=
    unary_cont_closed leftUnary centerUnary leftCenterSourceBound
  have sourceBoundRightUnary : UnaryHistory sourceBoundRight :=
    unary_cont_closed rightUnary centerUnary rightCenterSourceBound
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed precisionUnary targetTriangleUnary precisionTriangleHandoff
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary localNameUnary handoffLocalConsumer
  exact
    ⟨centerUnary, sourceBoundLeftUnary, sourceBoundRightUnary, targetBoundLeftUnary,
      targetBoundRightUnary, targetTriangleUnary, consumerUnary, leftCenterSourceBound,
      rightCenterSourceBound, targetTriangleRoute, precisionTriangleHandoff,
      handoffLocalConsumer, consumerPkg⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
