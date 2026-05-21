import BEDC.Derived.ApartnessRealUp
import BEDC.Derived.MetricUp.RealAlgOrderPositiveDistancePublicCorrespondence
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

theorem MetricRealalgorderApartnessPositiveReflection [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback separation provenance endpoint metricRow
      consumerRow dist witness budget classifier realAlg positiveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealAlgOrderConcreteInterface left right realAlg ->
      ApartnessRealMetricHandoffPacket left right radius window leftReadback rightReadback
        separation provenance endpoint bundle pkg ->
      MetricspaceRealDistanceCarrier left right dist radius witness budget classifier provenance
        realAlg ->
      UnaryHistory metricRow ->
      Cont radius realAlg positiveRead ->
      Cont endpoint metricRow consumerRow ->
      PkgSig bundle consumerRow pkg ->
        MetricDistanceWitness left right dist ∧ UnaryHistory positiveRead ∧
          UnaryHistory consumerRow ∧ Cont radius realAlg positiveRead ∧ hsame classifier dist := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame MetricDistanceWitness
  intro _realAlgInterface apartnessPacket metricCarrier metricRowUnary radiusRealAlgPositive
    endpointMetricConsumer consumerPkg
  have positivePackage :=
    MetricspaceRealalgorderPositiveDistancePublicCorrespondence metricCarrier
      radiusRealAlgPositive
  obtain ⟨distanceWitness, _leftUnary, _rightUnary, _distUnary, _radiusUnary,
    positiveUnary, positiveCont, _distRadiusBudget, classifierSame⟩ := positivePackage
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
    ⟨distanceWitness, positiveUnary, consumerUnary, positiveCont, classifierSame⟩

end BEDC.Derived.MetricUp
