import BEDC.Derived.DistributionUp
import BEDC.Derived.RiemannianMetricUp
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FisherInfoUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.DistributionUp
open BEDC.Derived.RiemannianMetricUp

def FisherInfoScorePacket
    (distribution metric parameter score expectation component provenance ledger : BHist) : Prop :=
  UnaryHistory distribution ∧ UnaryHistory metric ∧ UnaryHistory parameter ∧ UnaryHistory score ∧
    Cont distribution score expectation ∧ Cont metric expectation component ∧
      Cont component provenance ledger

theorem FisherInfoScorePacket_metric_component_transport
    {distribution distribution' metric metric' parameter score score' expectation expectation'
      component component' provenance ledger ledger' : BHist} :
    FisherInfoScorePacket distribution metric parameter score expectation component provenance ledger ->
      hsame distribution distribution' ->
        hsame metric metric' ->
          hsame score score' ->
            Cont distribution' score' expectation' ->
              Cont metric' expectation' component' ->
                Cont component' provenance ledger' ->
                  FisherInfoScorePacket distribution' metric' parameter score' expectation'
                      component' provenance ledger' ∧
                    hsame expectation expectation' ∧ hsame component component' ∧
                      hsame ledger ledger' := by
  intro packet sameDistribution sameMetric sameScore expectationRow componentRow ledgerRow
  have distributionUnary : UnaryHistory distribution' :=
    unary_transport packet.left sameDistribution
  have metricUnary : UnaryHistory metric' :=
    unary_transport packet.right.left sameMetric
  have scoreUnary : UnaryHistory score' :=
    unary_transport packet.right.right.right.left sameScore
  have sameExpectation : hsame expectation expectation' :=
    cont_respects_hsame sameDistribution sameScore packet.right.right.right.right.left
      expectationRow
  have sameComponent : hsame component component' :=
    cont_respects_hsame sameMetric sameExpectation packet.right.right.right.right.right.left
      componentRow
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameComponent (hsame_refl provenance)
      packet.right.right.right.right.right.right ledgerRow
  exact And.intro
    (And.intro distributionUnary
      (And.intro metricUnary
        (And.intro packet.right.right.left
          (And.intro scoreUnary
            (And.intro expectationRow (And.intro componentRow ledgerRow))))))
    (And.intro sameExpectation (And.intro sameComponent sameLedger))

def FisherInfoBHistScoreCarrier [AskSetup] [PackageSetup]
    (distribution metric parameter score expectation component provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  DistributionPushforwardSourceSpec distribution ∧
    RiemannianMetricSingletonFibreSurface parameter score metric ∧
      UnaryHistory parameter ∧ UnaryHistory score ∧
        Cont distribution score expectation ∧ Cont expectation metric component ∧
          PkgSig bundle provenance pkg ∧ Cont component provenance ledger

theorem FisherInfoBHistScoreCarrier_distribution_source_obligation [AskSetup] [PackageSetup]
    {distribution metric parameter score expectation component provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FisherInfoBHistScoreCarrier distribution metric parameter score expectation component
        provenance ledger bundle pkg ->
      DistributionPushforwardSourceSpec distribution ∧ UnaryHistory parameter ∧
        UnaryHistory score ∧ Cont distribution score expectation ∧
          PkgSig bundle provenance pkg := by
  intro carrier
  exact And.intro carrier.left
    (And.intro carrier.right.right.left
      (And.intro carrier.right.right.right.left
        (And.intro carrier.right.right.right.right.left
          carrier.right.right.right.right.right.right.left)))

theorem FisherInfoBHistScoreCarrier_expectation_ledger_exactness [AskSetup] [PackageSetup]
    {distribution metric parameter score expectation component provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FisherInfoBHistScoreCarrier distribution metric parameter score expectation component
        provenance ledger bundle pkg ->
      hsame expectation (append distribution score) ∧
        hsame component (append expectation metric) ∧ hsame ledger (append component provenance) ∧
          UnaryHistory score ∧ PkgSig bundle provenance pkg := by
  intro carrier
  exact And.intro carrier.right.right.right.right.left
    (And.intro carrier.right.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.right.right
        (And.intro carrier.right.right.right.left
          carrier.right.right.right.right.right.right.left)))

theorem FisherInfoBHistScoreCarrier_classifier_transport_obligation [AskSetup] [PackageSetup]
    {distribution distribution' metric metric' parameter parameter' score score' expectation
      expectation' component component' provenance ledger ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FisherInfoBHistScoreCarrier distribution metric parameter score expectation component
        provenance ledger bundle pkg ->
      hsame distribution distribution' ->
        hsame parameter parameter' ->
          hsame score score' ->
            hsame metric metric' ->
              DistributionPushforwardSourceSpec distribution' ->
                RiemannianMetricSingletonFibreSurface parameter' score' metric' ->
                  Cont distribution' score' expectation' ->
                    Cont expectation' metric' component' ->
                      Cont component' provenance ledger' ->
                        FisherInfoBHistScoreCarrier distribution' metric' parameter' score'
                            expectation' component' provenance ledger' bundle pkg ∧
                          hsame expectation expectation' ∧ hsame component component' ∧
                            hsame ledger ledger' := by
  intro carrier sameDistribution sameParameter sameScore sameMetric distributionSource'
  intro metricSurface' expectationRow' componentRow' ledgerRow'
  have parameterUnary' : UnaryHistory parameter' :=
    unary_transport carrier.right.right.left sameParameter
  have scoreUnary' : UnaryHistory score' :=
    unary_transport carrier.right.right.right.left sameScore
  have sameExpectation : hsame expectation expectation' :=
    cont_respects_hsame sameDistribution sameScore carrier.right.right.right.right.left
      expectationRow'
  have sameComponent : hsame component component' :=
    cont_respects_hsame sameExpectation sameMetric
      carrier.right.right.right.right.right.left componentRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameComponent (hsame_refl provenance)
      carrier.right.right.right.right.right.right.right ledgerRow'
  exact And.intro
    (And.intro distributionSource'
      (And.intro metricSurface'
        (And.intro parameterUnary'
          (And.intro scoreUnary'
            (And.intro expectationRow'
              (And.intro componentRow'
                (And.intro carrier.right.right.right.right.right.right.left ledgerRow')))))))
    (And.intro sameExpectation (And.intro sameComponent sameLedger))

end BEDC.Derived.FisherInfoUp
