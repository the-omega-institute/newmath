import BEDC.Derived.MetricUp.RealAlgOrderPositiveRadiusDistanceBoundary

namespace BEDC.Derived.MetricUp

open BEDC.Derived.ApartnessRealUp
open BEDC.Derived.RealAlgOrderUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricRealalgorderApartness_triangle_budget [AskSetup] [PackageSetup]
    {left middle right radiusLM radiusMR windowLM windowMR leftReadback middleReadback
      rightReadback separationLM separationMR provenanceLM provenanceMR endpointLM endpointMR
      metricRowLM metricRowMR consumerLM consumerMR distLM distMR witnessLM witnessMR budgetLM
      budgetMR classifierLM classifierMR realAlgLM realAlgMR positiveLM positiveMR : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealAlgOrderConcreteInterface left middle realAlgLM ->
      RealAlgOrderConcreteInterface middle right realAlgMR ->
        ApartnessRealMetricHandoffPacket left middle radiusLM windowLM leftReadback
          middleReadback separationLM provenanceLM endpointLM bundle pkg ->
        ApartnessRealMetricHandoffPacket middle right radiusMR windowMR middleReadback
          rightReadback separationMR provenanceMR endpointMR bundle pkg ->
        MetricspaceRealDistanceCarrier left middle distLM radiusLM witnessLM budgetLM
          classifierLM provenanceLM realAlgLM ->
        MetricspaceRealDistanceCarrier middle right distMR radiusMR witnessMR budgetMR
          classifierMR provenanceMR realAlgMR ->
        UnaryHistory metricRowLM ->
        UnaryHistory metricRowMR ->
        Cont radiusLM realAlgLM positiveLM ->
        Cont radiusMR realAlgMR positiveMR ->
        Cont endpointLM metricRowLM consumerLM ->
        Cont endpointMR metricRowMR consumerMR ->
        PkgSig bundle consumerLM pkg ->
        PkgSig bundle consumerMR pkg ->
          MetricDistanceWitness left middle distLM ∧
            MetricDistanceWitness middle right distMR ∧
              UnaryHistory positiveLM ∧ UnaryHistory positiveMR ∧
                UnaryHistory consumerLM ∧ UnaryHistory consumerMR ∧
                  PkgSig bundle consumerLM pkg ∧ PkgSig bundle consumerMR pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig MetricDistanceWitness
  intro realAlgLMInterface realAlgMRInterface apartnessLM apartnessMR metricCarrierLM
    metricCarrierMR metricRowLMUnary metricRowMRUnary radiusLMPositive radiusMRPositive
    endpointLMConsumer endpointMRConsumer consumerLMPkg consumerMRPkg
  have leftBoundary :=
    MetricRealalgorderPositiveRadiusDistanceBoundary realAlgLMInterface apartnessLM
      metricCarrierLM metricRowLMUnary radiusLMPositive endpointLMConsumer consumerLMPkg
  have rightBoundary :=
    MetricRealalgorderPositiveRadiusDistanceBoundary realAlgMRInterface apartnessMR
      metricCarrierMR metricRowMRUnary radiusMRPositive endpointMRConsumer consumerMRPkg
  exact
    ⟨leftBoundary.left,
      rightBoundary.left,
      leftBoundary.right.right.left,
      rightBoundary.right.right.left,
      leftBoundary.right.right.right.left,
      rightBoundary.right.right.right.left,
      leftBoundary.right.right.right.right.right.right,
      rightBoundary.right.right.right.right.right.right⟩

end BEDC.Derived.MetricUp
