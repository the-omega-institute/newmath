import BEDC.Derived.MetricUp.RealAlgOrderPositiveDistancePublicCorrespondence
import BEDC.Derived.S1Up.RealMetricBridgeBoundary

namespace BEDC.Derived.MetricUp

open BEDC.Derived.S1Up
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetricspaceSoneDistanceSourceBoundary
    {x y equation point metricLedger dist radius witness budget classifier provenance realAlg
      positiveRead : BHist} :
    SOneHistoryCarrier x y equation point →
      Cont point equation metricLedger →
        MetricspaceRealDistanceCarrier x y dist radius witness budget classifier provenance
          realAlg →
          Cont radius realAlg positiveRead →
            MetricDistanceWitness x y dist ∧ UnaryHistory point ∧ Cont x y point ∧
              Cont point equation metricLedger ∧ UnaryHistory positiveRead ∧
                Cont radius realAlg positiveRead ∧ hsame classifier dist ∧
                  hsame equation SOneUnitHistory := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory MetricDistanceWitness
  intro soneCarrier pointEquationMetric metricCarrier radiusRealAlgPositive
  have bridgeRows :=
    BEDC.Derived.S1Up.SOneRealMetricBridgeBoundary_public_rows soneCarrier
      pointEquationMetric
  have positiveRows :=
    MetricspaceRealalgorderPositiveDistancePublicCorrespondence metricCarrier
      radiusRealAlgPositive
  have publicRows := MetricspaceRealDistanceCarrier_public_law_package metricCarrier
  have pointUnary : UnaryHistory point :=
    unary_cont_left_factor pointEquationMetric bridgeRows.left
  exact
    ⟨publicRows.left, pointUnary, soneCarrier.right.right.right, pointEquationMetric,
      positiveRows.right.right.right.right.right.left, radiusRealAlgPositive,
      publicRows.right.right.right.left, bridgeRows.right.right.right⟩

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
