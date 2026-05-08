import BEDC.Derived.DistributionUp
import BEDC.Derived.RiemannianMetricUp
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FisherInfoUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem FisherInfoBHistScoreCarrier_score_row_carrier_obligation [AskSetup] [PackageSetup]
    {distribution metric parameter score expectation component provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FisherInfoBHistScoreCarrier distribution metric parameter score expectation component
        provenance ledger bundle pkg ->
      UnaryHistory parameter ∧ UnaryHistory score ∧ Cont distribution score expectation ∧
        UnaryHistory expectation ∧ Cont expectation metric component ∧ UnaryHistory component ∧
          Cont component provenance ledger := by
  intro carrier
  have distributionSource : DistributionPushforwardSourceSpec distribution := carrier.left
  have surface : RiemannianMetricSingletonFibreSurface parameter score metric :=
    carrier.right.left
  have parameterUnary : UnaryHistory parameter := carrier.right.right.left
  have scoreUnary : UnaryHistory score := carrier.right.right.right.left
  have expectationRow : Cont distribution score expectation :=
    carrier.right.right.right.right.left
  have componentRow : Cont expectation metric component :=
    carrier.right.right.right.right.right.left
  have ledgerRow : Cont component provenance ledger :=
    carrier.right.right.right.right.right.right.right
  have distributionUnary : UnaryHistory distribution := by
    cases distributionSource with
    | intro sourcePreimage source =>
        cases source with
        | intro sourceMeasure source =>
            cases source with
            | intro targetEvent source =>
                have rows :=
                  DistributionPushforwardCarrier_row source.left source.right
                exact unary_transport rows.right.left (hsame_symm rows.right.right)
  have expectationUnary : UnaryHistory expectation :=
    unary_cont_closed distributionUnary scoreUnary expectationRow
  have metricUnary : UnaryHistory metric := by
    have metricDisplay : hsame metric
        (BEDC.Derived.InnerProductUp.InnerProductSingletonForm score score) :=
      surface.right.right.right
    unfold BEDC.Derived.InnerProductUp.InnerProductSingletonForm at metricDisplay
    exact unary_transport (unary_e1_closed (unary_e1_closed unary_empty))
      (hsame_symm metricDisplay)
  have componentUnary : UnaryHistory component :=
    unary_cont_closed expectationUnary metricUnary componentRow
  exact And.intro parameterUnary
    (And.intro scoreUnary
      (And.intro expectationRow
        (And.intro expectationUnary
          (And.intro componentRow
            (And.intro componentUnary ledgerRow)))))

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

theorem FisherInfoBHistScoreCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {distribution metric parameter score expectation component provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FisherInfoBHistScoreCarrier distribution metric parameter score expectation component
        provenance ledger bundle pkg ->
      SemanticNameCert
          (fun endpoint : BHist =>
            exists score' expectation' component' ledger' : BHist,
              FisherInfoBHistScoreCarrier distribution metric parameter score' expectation'
                component' provenance ledger' bundle pkg ∧ hsame endpoint component')
          (fun endpoint : BHist =>
            exists score' expectation' component' ledger' : BHist,
              FisherInfoBHistScoreCarrier distribution metric parameter score' expectation'
                component' provenance ledger' bundle pkg ∧ hsame endpoint component')
          (fun endpoint : BHist =>
            exists score' expectation' component' ledger' : BHist,
              FisherInfoBHistScoreCarrier distribution metric parameter score' expectation'
                component' provenance ledger' bundle pkg ∧ hsame endpoint component')
          (fun left right : BHist =>
            (exists ls le lc ll : BHist,
              FisherInfoBHistScoreCarrier distribution metric parameter ls le lc provenance ll
                bundle pkg ∧ hsame left lc) ∧
            (exists rs re rc rl : BHist,
              FisherInfoBHistScoreCarrier distribution metric parameter rs re rc provenance rl
                bundle pkg ∧ hsame right rc) ∧
              hsame left right) ∧
        Cont distribution score expectation ∧ Cont expectation metric component ∧
          PkgSig bundle provenance pkg := by
  intro carrier
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          refine Exists.intro component ?_
          refine Exists.intro score ?_
          refine Exists.intro expectation ?_
          refine Exists.intro component ?_
          refine Exists.intro ledger ?_
          exact And.intro carrier (hsame_refl component)
        equiv_refl := by
          intro endpoint source
          exact And.intro source (And.intro source (hsame_refl endpoint))
        equiv_symm := by
          intro left right same
          exact And.intro same.right.left
            (And.intro same.left (hsame_symm same.right.right))
        equiv_trans := by
          intro left middle right sameLeftMiddle sameMiddleRight
          exact And.intro sameLeftMiddle.left
            (And.intro sameMiddleRight.right.left
              (hsame_trans sameLeftMiddle.right.right sameMiddleRight.right.right))
        carrier_respects_equiv := by
          intro left right same _source
          exact same.right.left
      }
      pattern_sound := by
        intro endpoint source
        exact source
      ledger_sound := by
        intro endpoint source
        exact source
    }
  · exact And.intro carrier.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.left
        carrier.right.right.right.right.right.right.left)

end BEDC.Derived.FisherInfoUp
