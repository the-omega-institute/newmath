import BEDC.Derived.MetricUp.RealAlgOrderApartnessDistanceScope
import BEDC.Derived.MetricUp.RealAlgOrderApartnessPositiveReflection
import BEDC.Derived.MetricUp.Transport

namespace BEDC.Derived.MetricUp

open BEDC.Derived.ApartnessRealUp
open BEDC.Derived.RealAlgOrderUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricRealalgorderPositiveRadiusDistanceBoundary [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback separation provenance endpoint metricRow
      consumerRow dist witness budget classifier realAlg positiveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealAlgOrderConcreteInterface left right realAlg →
      ApartnessRealMetricHandoffPacket left right radius window leftReadback rightReadback
        separation provenance endpoint bundle pkg →
      MetricspaceRealDistanceCarrier left right dist radius witness budget classifier provenance
        realAlg →
      UnaryHistory metricRow →
      Cont radius realAlg positiveRead →
      Cont endpoint metricRow consumerRow →
      PkgSig bundle consumerRow pkg →
        MetricDistanceWitness left right dist ∧ UnaryHistory radius ∧ UnaryHistory positiveRead ∧
          UnaryHistory consumerRow ∧ Cont radius realAlg positiveRead ∧ hsame classifier dist ∧
            PkgSig bundle consumerRow pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame MetricDistanceWitness
  intro realAlgInterface apartnessPacket metricCarrier metricRowUnary radiusRealAlgPositive
    endpointMetricConsumer consumerPkg
  have distanceScope :=
    MetricRealalgorderApartnessDistanceScope realAlgInterface apartnessPacket metricCarrier
      metricRowUnary endpointMetricConsumer consumerPkg
  have positiveReflection :=
    MetricRealalgorderApartnessPositiveReflection realAlgInterface apartnessPacket metricCarrier
      metricRowUnary radiusRealAlgPositive endpointMetricConsumer consumerPkg
  exact
    ⟨distanceScope.left,
      distanceScope.right.left,
      positiveReflection.right.left,
      positiveReflection.right.right.left,
      positiveReflection.right.right.right.left,
      distanceScope.right.right.right.left,
      distanceScope.right.right.right.right⟩

theorem MetricRealAlgOrder_positive_radius_distance_boundary {left right positive distance : BHist} :
    UnaryHistory left → UnaryHistory right → UnaryHistory positive → Cont left right distance →
      hsame distance positive → MetricDistanceWitness left right positive := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame MetricDistanceWitness
  intro leftUnary rightUnary positiveUnary distanceCont sameDistance
  exact
    And.intro leftUnary
      (And.intro rightUnary
        (And.intro positiveUnary
          (cont_result_hsame_transport distanceCont sameDistance)))

end BEDC.Derived.MetricUp
