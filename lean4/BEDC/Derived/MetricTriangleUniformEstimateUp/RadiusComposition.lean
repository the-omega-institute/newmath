import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_radius_composition
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
        sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
        targetTriangle transport route provenance localName bundle pkg ->
      Cont sourceBoundLeft precision sourceBoundRight ->
        Cont precision targetTriangle handoff ->
          PkgSig bundle sourceBoundRight pkg ->
            PkgSig bundle handoff pkg ->
              UnaryHistory center ∧ UnaryHistory precision ∧ UnaryHistory sourceBoundLeft ∧
                UnaryHistory sourceBoundRight ∧ UnaryHistory handoff ∧
                  Cont left center sourceBoundLeft ∧
                    Cont sourceBoundLeft precision sourceBoundRight ∧
                      Cont precision targetTriangle handoff ∧ PkgSig bundle localName pkg ∧
                        PkgSig bundle sourceBoundRight pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier sourceTriangle precisionTriangleHandoff sourceBoundPkg handoffPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    centerUnary, sourceBoundLeftUnary, sourceBoundRightUnary, precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRoute, _routeProvenanceLocalName, localNamePkg,
    _transportTargetTriangle⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed precisionUnary targetTriangleUnary precisionTriangleHandoff
  exact
    ⟨centerUnary, precisionUnary, sourceBoundLeftUnary, sourceBoundRightUnary, handoffUnary,
      leftCenterSourceBound, sourceTriangle, precisionTriangleHandoff, localNamePkg,
      sourceBoundPkg, handoffPkg⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
