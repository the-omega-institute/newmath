import BEDC.Derived.ApartnessRealUp
import BEDC.Derived.MetricUp.RealDistancePublicLawPackage
import BEDC.Derived.RealAlgOrderUp

namespace BEDC.Derived.MetricUp

open BEDC.Derived.ApartnessRealUp
open BEDC.Derived.RealAlgOrderUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricRealalgorderApartnessDistanceScope [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback separation provenance endpoint metricRow
      consumerRow dist witness budget classifier realAlg : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealAlgOrderConcreteInterface left right realAlg ->
      ApartnessRealMetricHandoffPacket left right radius window leftReadback rightReadback
        separation provenance endpoint bundle pkg ->
      MetricspaceRealDistanceCarrier left right dist radius witness budget classifier provenance
        realAlg ->
      UnaryHistory metricRow ->
      Cont endpoint metricRow consumerRow ->
      PkgSig bundle consumerRow pkg ->
        MetricDistanceWitness left right dist ∧ UnaryHistory radius ∧ UnaryHistory consumerRow ∧
          hsame classifier dist ∧ PkgSig bundle consumerRow pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame MetricDistanceWitness
  intro _realAlgInterface apartnessPacket metricCarrier metricRowUnary endpointMetricConsumer
    consumerPkg
  have publicPackage :=
    MetricspaceRealDistanceCarrier_public_law_package metricCarrier
  obtain ⟨distanceWitness, radiusUnary, _distRadiusBudget, classifierSame,
    _witnessBudgetProvenance⟩ := publicPackage
  have leftReadbackUnary : UnaryHistory leftReadback :=
    unary_cont_closed apartnessPacket.left apartnessPacket.right.right.right.left
      apartnessPacket.right.right.right.right.right.left
  have rightReadbackUnary : UnaryHistory rightReadback :=
    unary_cont_closed apartnessPacket.right.left apartnessPacket.right.right.right.left
      apartnessPacket.right.right.right.right.right.right.left
  have separationUnary : UnaryHistory separation :=
    unary_cont_closed leftReadbackUnary rightReadbackUnary
      apartnessPacket.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed separationUnary apartnessPacket.right.right.right.right.left
      apartnessPacket.right.right.right.right.right.right.right.right.left
  have consumerUnary : UnaryHistory consumerRow :=
    unary_cont_closed endpointUnary metricRowUnary endpointMetricConsumer
  exact
    ⟨distanceWitness, radiusUnary, consumerUnary, classifierSame, consumerPkg⟩

end BEDC.Derived.MetricUp
