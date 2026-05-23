import BEDC.Derived.CompactMetricUp

namespace BEDC.Derived.CompactMetricUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CompleteMetricUp
open BEDC.Derived.MetricUp
open BEDC.Derived.RatUp
open BEDC.Derived.TotallyBoundedUp

theorem CompactMetricPublicInterface_downstream_consumption_bridge
    {X : BHist -> Prop} {eps n x : BHist} {bundle : ProbeBundle BHist}
    {s M : BHist -> BHist} {limit : BHist} :
    CompactMetricCertificate X eps bundle s M limit ->
      UnaryHistory n ->
        X x ->
          X (s n) ->
            CompactMetricPublicExportSource X eps bundle s M limit ∧
              (exists center : BHist, InBundle center bundle ∧ X center ∧
                exists d : BHist, MetricDistanceWitness x center d ∧
                  RatHistoryClassifier d eps) ∧
                (exists limitDist : BHist,
                  MetricDistanceWitness (s n) limit limitDist ∧
                    Cont (s n) limit limitDist ∧ RatHistoryClassifier limitDist (M n)) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle InBundle MetricDistanceWitness
  intro certificate nUnary source streamSource
  cases certificate with
  | intro net complete =>
      have publicSource : CompactMetricPublicExportSource X eps bundle s M limit :=
        ⟨Exists.intro x source, net, complete⟩
      have netWitness :
          exists center : BHist, InBundle center bundle ∧ X center ∧
            exists d : BHist, MetricDistanceWitness x center d ∧
              RatHistoryClassifier d eps := by
        cases net.right.right source with
        | intro center centerData =>
            exact Exists.intro center
              (And.intro centerData.left
                (And.intro (net.right.left centerData.left) centerData.right))
      have limitWitness :
          exists limitDist : BHist,
            MetricDistanceWitness (s n) limit limitDist ∧
              Cont (s n) limit limitDist ∧ RatHistoryClassifier limitDist (M n) :=
        complete.right nUnary streamSource
      exact ⟨publicSource, netWitness, limitWitness⟩

end BEDC.Derived.CompactMetricUp
