import BEDC.Derived.MetricUp.SOneEquationDistanceFactorization
import BEDC.Derived.S1Up.RealMetricBridgeBoundary

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.S1Up

theorem MetricspaceS1RealalgorderConsumerFactorization
    {x y equation point dist radius witness budget classifier provenance realAlg positiveRead
      metricLedger : BHist} :
    SOneHistoryCarrier x y equation point ->
      MetricspaceRealDistanceCarrier x y dist radius witness budget classifier provenance realAlg ->
        Cont point equation metricLedger ->
          Cont radius realAlg positiveRead ->
            MetricDistanceWitness x y dist ∧ UnaryHistory point ∧ UnaryHistory metricLedger ∧
              UnaryHistory positiveRead ∧ Cont x y point ∧ Cont point equation metricLedger ∧
                Cont radius realAlg positiveRead ∧ hsame classifier dist := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory MetricDistanceWitness
  intro soneCarrier metricCarrier metricRoute positiveRoute
  have factorRows :=
    MetricRealalgorderSoneEquationDistanceFactorization soneCarrier metricCarrier positiveRoute
  have bridgeRows := SOneRealMetricBridgeBoundary_public_rows soneCarrier metricRoute
  exact
    ⟨factorRows.left, factorRows.right.left, bridgeRows.left,
      factorRows.right.right.right.left, factorRows.right.right.left, metricRoute,
      factorRows.right.right.right.right.left, factorRows.right.right.right.right.right⟩

end BEDC.Derived.MetricUp
