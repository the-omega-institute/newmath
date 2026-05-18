import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_center_bound_continuation
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName centerRead sourceRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
        sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
        targetTriangle transport route provenance localName bundle pkg ->
      Cont center precision centerRead ->
        Cont centerRead sourceBoundRight sourceRead ->
          Cont sourceRead targetTriangle targetRead ->
            PkgSig bundle targetRead pkg ->
              UnaryHistory center ∧ UnaryHistory precision ∧ UnaryHistory sourceBoundRight ∧
                UnaryHistory targetTriangle ∧ UnaryHistory centerRead ∧
                  UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧
                    Cont center precision centerRead ∧
                      Cont centerRead sourceBoundRight sourceRead ∧
                        Cont sourceRead targetTriangle targetRead ∧
                          PkgSig bundle localName pkg ∧ PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier centerPrecisionRead centerReadSourceBound sourceReadTarget targetPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    centerUnary, _sourceBoundLeftUnary, sourceBoundRightUnary, precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRoute, _routeProvenanceLocalName, localNamePkg,
    _transportTargetTriangle⟩ := carrier
  have centerReadUnary : UnaryHistory centerRead :=
    unary_cont_closed centerUnary precisionUnary centerPrecisionRead
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed centerReadUnary sourceBoundRightUnary centerReadSourceBound
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed sourceReadUnary targetTriangleUnary sourceReadTarget
  exact
    ⟨centerUnary, precisionUnary, sourceBoundRightUnary, targetTriangleUnary,
      centerReadUnary, sourceReadUnary, targetReadUnary, centerPrecisionRead,
      centerReadSourceBound, sourceReadTarget, localNamePkg, targetPkg⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
