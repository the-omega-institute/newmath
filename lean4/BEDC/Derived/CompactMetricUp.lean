import BEDC.Derived.CompleteMetricUp
import BEDC.Derived.TotallyBoundedUp
import BEDC.Derived.MetricUp

namespace BEDC.Derived.CompactMetricUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CompleteMetricUp
open BEDC.Derived.TotallyBoundedUp
open BEDC.Derived.MetricUp
open BEDC.Derived.RatUp

def CompactMetricCertificate (X : BHist -> Prop) (eps : BHist)
    (bundle : ProbeBundle BHist) (s M : BHist -> BHist) (limit : BHist) : Prop :=
  TotallyBoundedProbeBundleNet X eps bundle ∧ CompleteMetricLimitWitness X s M limit

theorem CompactMetricCertificate_hsame_transport {X : BHist -> Prop} {eps eps' : BHist}
    {bundle : ProbeBundle BHist} {s s' M M' : BHist -> BHist} {limit limit' : BHist} :
    (forall {h k : BHist}, hsame h k -> X h -> X k) ->
      hsame eps eps' ->
        (forall {n : BHist}, UnaryHistory n -> hsame (s n) (s' n)) ->
          (forall {n : BHist}, UnaryHistory n -> hsame (M n) (M' n)) ->
            hsame limit limit' -> CompactMetricCertificate X eps bundle s M limit ->
              CompactMetricCertificate X eps' bundle s' M' limit' := by
  intro carrierTransport sameEps streamTransport modulusTransport sameLimit certificate
  constructor
  · exact TotallyBoundedProbeBundleNet_coverage_hsame_transport sameEps certificate.left
  · exact CompleteMetricLimitWitness_hsame_transport carrierTransport streamTransport
      modulusTransport sameLimit certificate.right

theorem CompactMetricSingleton_certificate_package :
    InBundle BHist.Empty (ProbeBundle.Bcons BHist.Empty ProbeBundle.Bnil) ∧
      MetricDistanceWitness BHist.Empty BHist.Empty BHist.Empty ∧ hsame BHist.Empty BHist.Empty := by
  constructor
  · exact inBundle_cons_self BHist.Empty ProbeBundle.Bnil
  constructor
  · exact
      (MetricDistanceWitness_empty_distance_iff (x := BHist.Empty) (y := BHist.Empty)).mpr
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  · exact hsame_refl BHist.Empty

theorem CompactMetricPublicConstructor_package {X : BHist -> Prop} {eps x : BHist}
    {bundle : ProbeBundle BHist} {s M : BHist -> BHist} {limit : BHist} :
    CompactMetricCertificate X eps bundle s M limit -> X x ->
      TotallyBoundedProbeBundleNet X eps bundle ∧
        CompleteMetricLimitWitness X s M limit ∧
          exists center : BHist, InBundle center bundle ∧ X center ∧
            exists d : BHist, MetricDistanceWitness x center d ∧
              RatHistoryClassifier d eps := by
  intro certificate source
  cases certificate with
  | intro net complete =>
      constructor
      · exact net
      · constructor
        · exact complete
        · cases net.right.right source with
          | intro center centerData =>
              exact Exists.intro center
                (And.intro centerData.left
                  (And.intro (net.right.left centerData.left) centerData.right))

theorem CompactMetricHeineCantor_consumer_bridge {X : BHist -> Prop} {eps n : BHist}
    {bundle : ProbeBundle BHist} {s M : BHist -> BHist} {limit : BHist} :
    CompactMetricCertificate X eps bundle s M limit -> UnaryHistory n -> X (s n) ->
      (exists center : BHist, InBundle center bundle ∧ X center ∧
        exists d : BHist, MetricDistanceWitness (s n) center d ∧
          RatHistoryClassifier d eps) ∧
        exists limitDist : BHist, MetricDistanceWitness (s n) limit limitDist ∧
          Cont (s n) limit limitDist ∧ RatHistoryClassifier limitDist (M n) := by
  intro certificate nUnary source
  cases certificate with
  | intro net complete =>
      constructor
      · cases net.right.right source with
        | intro center centerData =>
            exact Exists.intro center
              (And.intro centerData.left
                (And.intro (net.right.left centerData.left) centerData.right))
      · exact complete.right nUnary source

end BEDC.Derived.CompactMetricUp
