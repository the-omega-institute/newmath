import BEDC.Derived.MetricUp.RealDistancePublicLawPackage
import BEDC.Derived.S1Up

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.Derived.S1Up

theorem MetricRealalgorderSoneEquationDistanceSymmetry
    {x y equation point x' y' equation' point' dist dist' radius witness budget classifier
      provenance realAlg : BHist} :
    SOneComponentClassifier x y equation point x' y' equation' point' ->
      MetricspaceRealDistanceCarrier x y dist radius witness budget classifier provenance realAlg ->
        MetricDistanceWitness y x dist' ->
          hsame dist dist' ∧ hsame equation equation' ∧ hsame point point' := by
  -- BEDC touchpoint anchor: BHist hsame MetricDistanceWitness
  intro soneClassifier metricCarrier reverseWitness
  have metricRows := MetricspaceRealDistanceCarrier_public_law_package metricCarrier
  have distanceSame : hsame dist dist' :=
    MetricDistanceWitness_symmetric_classifier metricRows.left reverseWitness
  have soneSame :=
    SOneHistoryCarrier_component_classifier_ledger_determinacy soneClassifier.left
      soneClassifier.right.left soneClassifier.right.right.left soneClassifier.right.right.right
  exact ⟨distanceSame, soneSame.left, soneSame.right⟩

end BEDC.Derived.MetricUp
