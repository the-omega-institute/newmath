import BEDC.Derived.CompleteMetricUp
import BEDC.Derived.TotallyBoundedUp
import BEDC.Derived.MetricUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CompactMetricUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CompleteMetricUp
open BEDC.Derived.TotallyBoundedUp
open BEDC.Derived.MetricUp
open BEDC.Derived.RatUp
open BEDC.FKernel.NameCert

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

theorem CompactMetricCertificate_component_stability {X : BHist -> Prop} {eps eps' : BHist}
    {bundle : ProbeBundle BHist} {s s' M M' : BHist -> BHist} {limit limit' : BHist} :
    (forall {h k : BHist}, hsame h k -> X h -> X k) ->
      hsame eps eps' ->
        (forall {n : BHist}, UnaryHistory n -> hsame (s n) (s' n)) ->
          (forall {n : BHist}, UnaryHistory n -> hsame (M n) (M' n)) ->
            hsame limit limit' -> CompactMetricCertificate X eps bundle s M limit ->
              TotallyBoundedProbeBundleNet X eps' bundle ∧
                CompleteMetricLimitWitness X s' M' limit' ∧
                  CompactMetricCertificate X eps' bundle s' M' limit' := by
  intro carrierTransport sameEps streamTransport modulusTransport sameLimit certificate
  have transportedNet : TotallyBoundedProbeBundleNet X eps' bundle :=
    TotallyBoundedProbeBundleNet_coverage_hsame_transport sameEps certificate.left
  have transportedLimit : CompleteMetricLimitWitness X s' M' limit' :=
    CompleteMetricLimitWitness_hsame_transport carrierTransport streamTransport
      modulusTransport sameLimit certificate.right
  exact And.intro transportedNet
    (And.intro transportedLimit (And.intro transportedNet transportedLimit))

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

theorem CompactMetricCertificate_scope {X : BHist -> Prop} {eps : BHist}
    {bundle : ProbeBundle BHist} {s M : BHist -> BHist} {limit : BHist} :
    CompactMetricCertificate X eps bundle s M limit ->
      TotallyBoundedProbeBundleNet X eps bundle ∧
        CompleteMetricLimitWitness X s M limit ∧
          (forall {x : BHist}, X x ->
            exists center : BHist, InBundle center bundle ∧ X center ∧
              exists d : BHist,
                MetricDistanceWitness x center d ∧ RatHistoryClassifier d eps) ∧
            (forall {n : BHist}, UnaryHistory n -> X (s n) ->
              exists d : BHist,
                MetricDistanceWitness (s n) limit d ∧ Cont (s n) limit d ∧
                  RatHistoryClassifier d (M n)) := by
  intro certificate
  cases certificate with
  | intro net complete =>
      constructor
      · exact net
      · constructor
        · exact complete
        · constructor
          · intro x source
            cases net.right.right source with
            | intro center centerData =>
                cases centerData.right with
                | intro d distanceData =>
                    exact ⟨center, centerData.left, net.right.left centerData.left, d,
                      distanceData.left, distanceData.right⟩
          · intro n nUnary source
            exact complete.right nUnary source

theorem CompactMetricCertificate_metric_distance_transport {X : BHist -> Prop}
    {eps x x' y y' d d' : BHist} {bundle : ProbeBundle BHist} {s M : BHist -> BHist}
    {limit : BHist} :
    CompactMetricCertificate X eps bundle s M limit ->
      (forall {h k : BHist}, hsame h k -> X h -> X k) -> X x -> X y ->
        hsame x x' -> hsame y y' -> MetricDistanceWitness x y d ->
          MetricDistanceWitness x' y' d' ->
            X x' ∧ X y' ∧ hsame d d' ∧ MetricDistanceWitness x' y' d' := by
  intro certificate carrierTransport source target sameX sameY leftDistance rightDistance
  have transportedX : X x' := carrierTransport sameX source
  have transportedY : X y' := carrierTransport sameY target
  have sameDistance : hsame d d' :=
    MetricDistanceWitness_hsame_result_deterministic sameX sameY leftDistance rightDistance
  exact And.intro transportedX
    (And.intro transportedY (And.intro sameDistance rightDistance))

theorem CompactMetricTotallyBoundedNet_obligation {X : BHist -> Prop} {eps eps' x : BHist}
    {bundle : ProbeBundle BHist} {s M : BHist -> BHist} {limit : BHist} :
    CompactMetricCertificate X eps bundle s M limit -> hsame eps eps' -> X x ->
      TotallyBoundedProbeBundleNet X eps' bundle ∧
        exists center : BHist, InBundle center bundle ∧ X center ∧
          exists d : BHist, MetricDistanceWitness x center d ∧
            RatHistoryClassifier d eps' := by
  intro certificate sameEps source
  have transportedNet : TotallyBoundedProbeBundleNet X eps' bundle :=
    TotallyBoundedProbeBundleNet_coverage_hsame_transport sameEps certificate.left
  constructor
  · exact transportedNet
  · cases transportedNet.right.right source with
    | intro center centerData =>
        exact Exists.intro center
          (And.intro centerData.left
            (And.intro (transportedNet.right.left centerData.left) centerData.right))

theorem CompactMetricLedger_exactness_obligation {X : BHist -> Prop} {eps x n : BHist}
    {bundle : ProbeBundle BHist} {s M : BHist -> BHist} {limit : BHist} :
    CompactMetricCertificate X eps bundle s M limit -> X x -> UnaryHistory n ->
      X (s n) ->
        TotallyBoundedProbeBundleNet X eps bundle ∧
          CompleteMetricLimitWitness X s M limit ∧
            (exists center : BHist, InBundle center bundle ∧ X center ∧
              exists d : BHist, MetricDistanceWitness x center d ∧
                RatHistoryClassifier d eps) ∧
              (exists limitDist : BHist,
                MetricDistanceWitness (s n) limit limitDist ∧
                  Cont (s n) limit limitDist ∧ RatHistoryClassifier limitDist (M n)) := by
  intro certificate source nUnary streamSource
  cases certificate with
  | intro net complete =>
      constructor
      · exact net
      · constructor
        · exact complete
        · constructor
          · cases net.right.right source with
            | intro center centerData =>
                cases centerData.right with
                | intro d distanceData =>
                    exact Exists.intro center
                      (And.intro centerData.left
                        (And.intro (net.right.left centerData.left)
                          (Exists.intro d distanceData)))
          · exact complete.right nUnary streamSource

theorem CompactMetricDownstreamConsumer_boundary {X : BHist -> Prop} {eps x n : BHist}
    {bundle : ProbeBundle BHist} {s M : BHist -> BHist} {limit : BHist} :
    CompactMetricCertificate X eps bundle s M limit -> X x -> UnaryHistory n -> X (s n) ->
      (exists center : BHist, InBundle center bundle ∧ X center ∧
        exists d : BHist, MetricDistanceWitness x center d ∧ RatHistoryClassifier d eps) ∧
        (exists limitDist : BHist, MetricDistanceWitness (s n) limit limitDist ∧
          Cont (s n) limit limitDist ∧ RatHistoryClassifier limitDist (M n)) := by
  intro certificate source nUnary streamSource
  have publicPackage := CompactMetricPublicConstructor_package certificate source
  have consumerBridge := CompactMetricHeineCantor_consumer_bridge certificate nUnary streamSource
  exact And.intro publicPackage.right.right consumerBridge.right

theorem CompactMetricCertificate_public_export_surface {X : BHist -> Prop} {eps x : BHist}
    {bundle : ProbeBundle BHist} {s M : BHist -> BHist} {limit : BHist} :
    CompactMetricCertificate X eps bundle s M limit -> X x ->
      SemanticNameCert
          (fun row : BHist =>
            X row ∨ (exists center : BHist, InBundle center bundle ∧ hsame row center) ∨
              hsame row limit)
          (fun row : BHist =>
            X row ∨ (exists center : BHist, InBundle center bundle ∧ hsame row center) ∨
              hsame row limit)
          (fun row : BHist =>
            X row ∨ (exists center : BHist, InBundle center bundle ∧ hsame row center) ∨
              hsame row limit)
          (fun left right : BHist =>
            (X left ∨ (exists center : BHist, InBundle center bundle ∧ hsame left center) ∨
                hsame left limit) ∧
              (X right ∨
                  (exists center : BHist, InBundle center bundle ∧ hsame right center) ∨
                    hsame right limit) ∧
                hsame left right) ∧
        TotallyBoundedProbeBundleNet X eps bundle ∧ CompleteMetricLimitWitness X s M limit := by
  intro certificate source
  let publicSurface : BHist -> Prop :=
    fun row : BHist =>
      X row ∨ (exists center : BHist, InBundle center bundle ∧ hsame row center) ∨
        hsame row limit
  have sourcePublic : publicSurface x :=
    Or.inl source
  have publicSelf : forall {row : BHist}, publicSurface row ->
      (publicSurface row ∧ publicSurface row ∧ hsame row row) := by
    intro row rowPublic
    exact And.intro rowPublic (And.intro rowPublic (hsame_refl row))
  have publicSymm : forall {left right : BHist},
      (publicSurface left ∧ publicSurface right ∧ hsame left right) ->
        publicSurface right ∧ publicSurface left ∧ hsame right left := by
    intro left right classified
    exact And.intro classified.right.left
      (And.intro classified.left (hsame_symm classified.right.right))
  have publicTrans : forall {left middle right : BHist},
      (publicSurface left ∧ publicSurface middle ∧ hsame left middle) ->
        (publicSurface middle ∧ publicSurface right ∧ hsame middle right) ->
          publicSurface left ∧ publicSurface right ∧ hsame left right := by
    intro left middle right leftClass rightClass
    exact And.intro leftClass.left
      (And.intro rightClass.right.left
        (hsame_trans leftClass.right.right rightClass.right.right))
  have publicTransport : forall {left right : BHist},
      (publicSurface left ∧ publicSurface right ∧ hsame left right) ->
        publicSurface left -> publicSurface right := by
    intro left right classified _leftPublic
    exact classified.right.left
  exact And.intro
    {
      core := {
        carrier_inhabited := Exists.intro x sourcePublic
        equiv_refl := by
          intro row rowPublic
          exact publicSelf rowPublic
        equiv_symm := by
          intro left right classified
          exact publicSymm classified
        equiv_trans := by
          intro left middle right leftClass rightClass
          exact publicTrans leftClass rightClass
        carrier_respects_equiv := by
          intro left right classified leftPublic
          exact publicTransport classified leftPublic
      }
      pattern_sound := by
        intro _row rowPublic
        exact rowPublic
      ledger_sound := by
        intro _row rowPublic
        exact rowPublic
    }
    (And.intro certificate.left certificate.right)

end BEDC.Derived.CompactMetricUp
