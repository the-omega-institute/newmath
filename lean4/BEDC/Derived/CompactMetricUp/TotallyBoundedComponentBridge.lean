import BEDC.Derived.CompactMetricUp

namespace BEDC.Derived.CompactMetricUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.Derived.MetricUp
open BEDC.Derived.RatUp
open BEDC.Derived.TotallyBoundedUp

theorem TotallyBoundedCompactMetric_component_bridge {X : BHist → Prop} {eps : BHist}
    {bundle : ProbeBundle BHist} {s M : BHist → BHist} {limit : BHist} :
    CompactMetricCertificate X eps bundle s M limit →
      TotallyBoundedProbeBundleNet X eps bundle ∧
        (∀ {x : BHist}, X x →
          ∃ center : BHist, InBundle center bundle ∧ X center ∧
            ∃ d : BHist, MetricDistanceWitness x center d ∧ RatHistoryClassifier d eps) := by
  intro certificate
  cases certificate with
  | intro net _complete =>
      constructor
      · exact net
      · intro x source
        cases net.right.right source with
        | intro center centerData =>
            exact Exists.intro center
              (And.intro centerData.left
                (And.intro (net.right.left centerData.left) centerData.right))

end BEDC.Derived.CompactMetricUp
