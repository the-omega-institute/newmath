import BEDC.Derived.MetricUp.RealAlgOrderApartnessPositiveReflection

namespace BEDC.Derived.MetricUp

open BEDC.Derived.ApartnessRealUp
open BEDC.Derived.RealAlgOrderUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealAlgOrderApartnessMetricSymmetricSeparation [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback separation provenance endpoint
      swappedRightReadback swappedLeftReadback swappedSeparation swappedEndpoint dist witness
      budget classifier realAlg metricRow consumerRow positiveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealAlgOrderConcreteInterface right left realAlg ->
      ApartnessRealMetricHandoffPacket left right radius window leftReadback rightReadback
        separation provenance endpoint bundle pkg ->
      Cont right window swappedRightReadback ->
      Cont left window swappedLeftReadback ->
      Cont swappedRightReadback swappedLeftReadback swappedSeparation ->
      Cont swappedSeparation provenance swappedEndpoint ->
      PkgSig bundle swappedEndpoint pkg ->
      MetricspaceRealDistanceCarrier right left dist radius witness budget classifier provenance
        realAlg ->
      UnaryHistory metricRow ->
      Cont radius realAlg positiveRead ->
      Cont swappedEndpoint metricRow consumerRow ->
      PkgSig bundle consumerRow pkg ->
        ApartnessRealMetricHandoffPacket right left radius window swappedRightReadback
            swappedLeftReadback swappedSeparation provenance swappedEndpoint bundle pkg ∧
          MetricDistanceWitness right left dist ∧ UnaryHistory positiveRead ∧
            UnaryHistory consumerRow ∧ Cont radius realAlg positiveRead ∧
              hsame classifier dist := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame MetricDistanceWitness
  intro realAlgInterface packet swappedRightWindow swappedLeftWindow swappedSeparationRow
    swappedEndpointRow swappedEndpointPkg metricCarrier metricRowUnary radiusRealAlgPositive
    swappedEndpointMetricConsumer consumerPkg
  have swappedPacket :
      ApartnessRealMetricHandoffPacket right left radius window swappedRightReadback
          swappedLeftReadback swappedSeparation provenance swappedEndpoint bundle pkg := by
    exact
      ⟨packet.right.left,
        packet.left,
        packet.right.right.left,
        packet.right.right.right.left,
        packet.right.right.right.right.left,
        swappedRightWindow,
        swappedLeftWindow,
        swappedSeparationRow,
        swappedEndpointRow,
        swappedEndpointPkg⟩
  have reflected :=
    MetricRealalgorderApartnessPositiveReflection realAlgInterface swappedPacket metricCarrier
      metricRowUnary radiusRealAlgPositive swappedEndpointMetricConsumer consumerPkg
  exact
    ⟨swappedPacket, reflected.left, reflected.right.left, reflected.right.right.left,
      reflected.right.right.right.left, reflected.right.right.right.right⟩

end BEDC.Derived.MetricUp
