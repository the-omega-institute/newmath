import BEDC.Derived.BanachUp

namespace BEDC.Derived.BanachUp

open BEDC.FKernel.Hist
open BEDC.Derived.FieldUp
open BEDC.Derived.MetricUp
open BEDC.Derived.VecSpaceUp

theorem BanachMetricInducedByNorm {x y : BHist} :
    BanachSingletonCarrier x ->
      BanachSingletonCarrier y ->
        MetricDistanceWitness x y BHist.Empty ∧ BanachSingletonClassifier x y ∧
          VecSpaceSingletonClassifier x y ∧ FieldSingletonClassifier x y := by
  -- BEDC touchpoint anchor: BHist hsame BanachSingletonCarrier MetricDistanceWitness
  intro carrierX carrierY
  have distance : MetricDistanceWitness x y BHist.Empty :=
    MetricDistanceWitness_empty_distance_iff.mpr (And.intro carrierX.left carrierY.left)
  have rootRows :=
    BanachRoot_carrier_classifier_obligation carrierX carrierY
  exact
    And.intro distance
      (And.intro rootRows.left (And.intro rootRows.right.left rootRows.right.right.left))

theorem BanachClassifierTransportObligation {x x' y y' : BHist} :
    BanachSingletonCarrier x ->
      BanachSingletonCarrier x' ->
        BanachSingletonCarrier y ->
          BanachSingletonCarrier y' ->
            hsame x x' ->
              hsame y y' ->
                BanachSingletonClassifier x x' ∧ BanachSingletonClassifier y y' ∧
                  MetricDistanceWitness x y BHist.Empty ∧
                    MetricDistanceWitness x' y' BHist.Empty := by
  -- BEDC touchpoint anchor: BHist hsame BanachSingletonCarrier MetricDistanceWitness
  intro carrierX carrierX' carrierY carrierY' sameXX' sameYY'
  have classifiedXX' : BanachSingletonClassifier x x' :=
    And.intro carrierX (And.intro carrierX' sameXX')
  have classifiedYY' : BanachSingletonClassifier y y' :=
    And.intro carrierY (And.intro carrierY' sameYY')
  have distanceXY : MetricDistanceWitness x y BHist.Empty :=
    MetricDistanceWitness_empty_distance_iff.mpr (And.intro carrierX.left carrierY.left)
  have distanceX'Y' : MetricDistanceWitness x' y' BHist.Empty :=
    MetricDistanceWitness_empty_distance_iff.mpr (And.intro carrierX'.left carrierY'.left)
  exact
    And.intro classifiedXX'
      (And.intro classifiedYY' (And.intro distanceXY distanceX'Y'))

end BEDC.Derived.BanachUp
