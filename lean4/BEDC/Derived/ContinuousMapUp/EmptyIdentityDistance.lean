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

end BEDC.Derived.ContinuousMapUp
