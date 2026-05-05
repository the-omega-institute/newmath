import BEDC.Derived.ContinuousMapUp

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.ContinuousUp
open BEDC.Derived.MetricUp

theorem ContinuousMapCarrier_empty_identity_distance_deterministic
    {source map target modulus cert distance displayedSource displayedTarget : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      ContinuousMapCarrier source BHist.Empty source BHist.Empty source displayedSource ->
        ContinuousMapCarrier target BHist.Empty target BHist.Empty target displayedTarget ->
          hsame displayedSource (append source source) ∧
            hsame displayedTarget (append target target) := by
  intro carrier displayedSourceCarrier displayedTargetCarrier
  have identities := ContinuousMapCarrier_empty_identities_closed carrier
  have sourceCompare :=
    ContinuousMapCarrier_target_cert_distance_deterministic displayedSourceCarrier
      identities.left
  have targetCompare :=
    ContinuousMapCarrier_target_cert_distance_deterministic displayedTargetCarrier
      identities.right
  exact And.intro sourceCompare.right.right.left targetCompare.right.right.left

theorem ContinuousMap_empty_identity_metric_witness_iff
    {x y x' y' d mx my cx cy : BHist} :
    ContinuousFunctionCarrier x BHist.Empty x' mx cx ->
      ContinuousFunctionCarrier y BHist.Empty y' my cy ->
        (MetricDistanceWitness x' y' d ↔ MetricDistanceWitness x y d) := by
  intro left right
  constructor
  · intro imageWitness
    exact ContinuousMap_empty_identity_metric_witness_reflects left right imageWitness
  · intro sourceWitness
    have sameX : hsame x x' :=
      hsame_symm (ContinuousFunctionCarrier_empty_map_iff.mp left).left
    have sameY : hsame y y' :=
      hsame_symm (ContinuousFunctionCarrier_empty_map_iff.mp right).left
    have transported :=
      MetricDistanceWitness_hsame_fields_transport sameX sameY (hsame_refl d) sourceWitness
    exact
      And.intro transported.left
        (And.intro transported.right.left
          (And.intro transported.right.right.left transported.right.right.right))

end BEDC.Derived.ContinuousMapUp
