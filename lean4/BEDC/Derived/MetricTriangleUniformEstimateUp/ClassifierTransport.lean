import BEDC.Derived.MetricTriangleUniformEstimateUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_classifier_transport [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName sourceMetric' targetMetric' graph' left' right' center' sourceBoundLeft'
      sourceBoundRight' precision' targetBoundLeft' targetBoundRight' targetTriangle'
      transport' route' provenance' localName' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg ->
      hsame sourceMetric sourceMetric' ->
      hsame targetMetric targetMetric' ->
      hsame graph graph' ->
      hsame left left' ->
      hsame right right' ->
      hsame center center' ->
      hsame sourceBoundLeft sourceBoundLeft' ->
      hsame sourceBoundRight sourceBoundRight' ->
      hsame precision precision' ->
      hsame targetBoundLeft targetBoundLeft' ->
      hsame targetBoundRight targetBoundRight' ->
      hsame targetTriangle targetTriangle' ->
      hsame transport transport' ->
      hsame route route' ->
      hsame provenance provenance' ->
      hsame localName localName' ->
      PkgSig bundle localName' pkg ->
        MetricTriangleUniformEstimateCarrier sourceMetric' targetMetric' graph' left' right'
          center' sourceBoundLeft' sourceBoundRight' precision' targetBoundLeft'
          targetBoundRight' targetTriangle' transport' route' provenance' localName'
          bundle pkg ∧ hsame transport' targetTriangle' ∧
            PkgSig bundle localName' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier sameSourceMetric sameTargetMetric sameGraph sameLeft sameRight sameCenter
    sameSourceBoundLeft sameSourceBoundRight samePrecision sameTargetBoundLeft
    sameTargetBoundRight sameTargetTriangle sameTransportRow sameRoute sameProvenance
    sameLocalName localNamePkg'
  obtain ⟨sourceMetricUnary, targetMetricUnary, graphUnary, leftUnary, rightUnary,
    centerUnary, sourceBoundLeftUnary, sourceBoundRightUnary, precisionUnary,
    targetBoundLeftUnary, targetBoundRightUnary, targetTriangleUnary, transportUnary,
    routeUnary, provenanceUnary, localNameUnary, leftCenterSourceBound,
    rightCenterSourceBound, targetTriangleRoute, routeProvenanceLocalName,
    _localNamePkg, transportTargetTriangle⟩ := carrier
  have transportTargetTriangle' : hsame transport' targetTriangle' :=
    hsame_trans (hsame_trans (hsame_symm sameTransportRow) transportTargetTriangle)
      sameTargetTriangle
  have transportedCarrier :
      MetricTriangleUniformEstimateCarrier sourceMetric' targetMetric' graph' left' right'
        center' sourceBoundLeft' sourceBoundRight' precision' targetBoundLeft'
        targetBoundRight' targetTriangle' transport' route' provenance' localName'
        bundle pkg := by
    exact
      ⟨unary_transport sourceMetricUnary sameSourceMetric,
        unary_transport targetMetricUnary sameTargetMetric,
        unary_transport graphUnary sameGraph,
        unary_transport leftUnary sameLeft,
        unary_transport rightUnary sameRight,
        unary_transport centerUnary sameCenter,
        unary_transport sourceBoundLeftUnary sameSourceBoundLeft,
        unary_transport sourceBoundRightUnary sameSourceBoundRight,
        unary_transport precisionUnary samePrecision,
        unary_transport targetBoundLeftUnary sameTargetBoundLeft,
        unary_transport targetBoundRightUnary sameTargetBoundRight,
        unary_transport targetTriangleUnary sameTargetTriangle,
        unary_transport transportUnary sameTransportRow,
        unary_transport routeUnary sameRoute,
        unary_transport provenanceUnary sameProvenance,
        unary_transport localNameUnary sameLocalName,
        cont_hsame_transport sameLeft sameCenter sameSourceBoundLeft leftCenterSourceBound,
        cont_hsame_transport sameRight sameCenter sameSourceBoundRight rightCenterSourceBound,
        cont_hsame_transport sameTargetBoundLeft sameTargetBoundRight sameTargetTriangle
          targetTriangleRoute,
        cont_hsame_transport sameRoute sameProvenance sameLocalName routeProvenanceLocalName,
        localNamePkg', transportTargetTriangle'⟩
  exact ⟨transportedCarrier, transportTargetTriangle', localNamePkg'⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
