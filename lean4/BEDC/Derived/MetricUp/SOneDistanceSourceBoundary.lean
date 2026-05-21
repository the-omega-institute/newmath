import BEDC.Derived.MetricUp.RealAlgOrderPositiveDistancePublicCorrespondence
import BEDC.Derived.S1Up.RealMetricBridgeBoundary

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.S1Up

theorem MetricspaceSOneDistanceSourceBoundary
    {x y equation point dist radius witness budget classifier provenance realAlg positiveRead
      metricLedger : BHist} :
    SOneHistoryCarrier x y equation point ->
      MetricspaceRealDistanceCarrier x y dist radius witness budget classifier provenance realAlg ->
        Cont point equation metricLedger ->
          Cont radius realAlg positiveRead ->
            MetricDistanceWitness x y dist ∧ SOneProductHistoryCarrier point ∧
              hsame equation SOneUnitHistory ∧ UnaryHistory metricLedger ∧
                UnaryHistory positiveRead ∧ Cont point equation metricLedger ∧
                  Cont radius realAlg positiveRead ∧ hsame classifier dist := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory MetricDistanceWitness
  intro soneCarrier metricCarrier metricRoute positiveRoute
  have soneRows := SOneRealMetricBridgeBoundary_public_rows soneCarrier metricRoute
  have metricRows :=
    MetricspaceRealalgorderPositiveDistancePublicCorrespondence metricCarrier positiveRoute
  exact
    ⟨metricRows.left, soneRows.right.right.left, soneRows.right.right.right,
      soneRows.left, metricRows.right.right.right.right.right.left, metricRoute,
      metricRows.right.right.right.right.right.right.left,
      metricRows.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.MetricUp
