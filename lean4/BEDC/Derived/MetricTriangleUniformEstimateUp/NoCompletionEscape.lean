import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_no_completion_escape [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName sourceRead targetRead handoff consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg ->
      Cont sourceBoundLeft precision sourceRead ->
        Cont targetTriangle localName targetRead ->
          Cont sourceRead targetRead handoff ->
            Cont handoff localName consumer ->
              PkgSig bundle handoff pkg ->
                PkgSig bundle consumer pkg ->
                  UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧
                    UnaryHistory handoff ∧ UnaryHistory consumer ∧
                      Cont sourceBoundLeft precision sourceRead ∧
                        Cont targetTriangle localName targetRead ∧
                          Cont sourceRead targetRead handoff ∧
                            Cont handoff localName consumer ∧
                              PkgSig bundle localName pkg ∧ PkgSig bundle handoff pkg ∧
                                PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sourcePrecisionRead targetTriangleRead readHandoff handoffConsumer
    handoffPkg consumerPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    _centerUnary, sourceBoundLeftUnary, _sourceBoundRightUnary, precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRoute, _routeProvenanceLocalName,
    localNamePkg, _transportTargetTriangle⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceBoundLeftUnary precisionUnary sourcePrecisionRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed targetTriangleUnary localNameUnary targetTriangleRead
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed sourceReadUnary targetReadUnary readHandoff
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary localNameUnary handoffConsumer
  exact
    ⟨sourceReadUnary, targetReadUnary, handoffUnary, consumerUnary, sourcePrecisionRead,
      targetTriangleRead, readHandoff, handoffConsumer, localNamePkg, handoffPkg,
      consumerPkg⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
