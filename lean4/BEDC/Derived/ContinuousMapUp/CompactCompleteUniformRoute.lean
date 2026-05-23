import BEDC.Derived.CompactMetricUp
import BEDC.Derived.ContinuousMapUp

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CompactMetricUp
open BEDC.Derived.CompleteMetricUp
open BEDC.Derived.MetricUp
open BEDC.Derived.RatUp
open BEDC.Derived.TotallyBoundedUp

theorem ContinuousMapCarrier_compact_complete_uniform_route {X : BHist -> Prop}
    {source map target modulus cert distance eps n : BHist} {bundle : ProbeBundle BHist}
    {s M : BHist -> BHist} {limit : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      CompactMetricCertificate X eps bundle s M limit ->
        UnaryHistory n ->
          X (s n) ->
            MetricDistanceWitness source target distance ∧
              TotallyBoundedProbeBundleNet X eps bundle ∧
                CompleteMetricLimitWitness X s M limit ∧
                  exists d : BHist,
                    MetricDistanceWitness (s n) limit d ∧ Cont (s n) limit d ∧
                      RatHistoryClassifier d (M n) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont UnaryHistory RatHistoryClassifier
  intro carrier certificate nUnary sourcePoint
  obtain ⟨_continuousCarrier, distanceWitness⟩ := carrier
  obtain ⟨net, completeLimit⟩ := certificate
  exact ⟨distanceWitness, net, completeLimit, completeLimit.right nUnary sourcePoint⟩

end BEDC.Derived.ContinuousMapUp
