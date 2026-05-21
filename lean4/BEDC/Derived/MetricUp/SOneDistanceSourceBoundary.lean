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

end BEDC.Derived.MetricUp
