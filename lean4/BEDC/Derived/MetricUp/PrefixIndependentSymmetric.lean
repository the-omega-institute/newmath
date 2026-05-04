import BEDC.Derived.MetricUp
import BEDC.Derived.MetricUp.DepthZero

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_visible_context_prefix_independent_symmetric_classifier
    {p q p' q' x y dxy dyx : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness (append p' y) (append x q') (append (append p' dyx) q') ->
        hsame dxy dyx := by
  intro forward reverse
  have forwardCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := dxy)).mp forward
  have reverseCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p') (q := q') (x := y) (y := x)
      (d := dyx)).mp reverse
  exact MetricDistanceWitness_symmetric_classifier forwardCentral.2.2 reverseCentral.2.2

theorem MetricDistanceWitness_prefix_independent_symmetric_zero_depth_collapse
    {p q p' q' x y dxy dyx : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness (append p' y) (append x q') (append (append p' dyx) q') ->
        MetricDistanceDepth dxy = 0 ->
          hsame dxy dyx ∧ MetricDistanceDepth dyx = 0 ∧
            hsame x BHist.Empty ∧ hsame y BHist.Empty := by
  intro forward reverse depthZero
  have sameDistance : hsame dxy dyx :=
    MetricDistanceWitness_visible_context_prefix_independent_symmetric_classifier forward reverse
  have forwardCollapse :
      hsame dxy BHist.Empty ∧ hsame x BHist.Empty ∧ hsame y BHist.Empty :=
    MetricDistanceWitness_visible_context_depth_zero_collapse forward depthZero
  have reverseCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p') (q := q') (x := y) (y := x)
      (d := dyx)).mp reverse
  have reverseDepth : MetricDistanceDepth dyx = 0 :=
    MetricDistanceWitness_empty_endpoints_depth_zero reverseCentral.2.2
      forwardCollapse.2.2 forwardCollapse.2.1
  exact
    And.intro sameDistance
      (And.intro reverseDepth (And.intro forwardCollapse.2.1 forwardCollapse.2.2))

theorem MetricDistanceWitness_visible_context_prefix_independent_symmetric_zero_depth_collapse
    {p q p' q' x y dxy dyx : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness (append p' y) (append x q') (append (append p' dyx) q') ->
        MetricDistanceDepth dxy = 0 ->
          hsame dxy dyx ∧ MetricDistanceDepth dyx = 0 ∧ hsame x BHist.Empty ∧
            hsame y BHist.Empty := by
  exact MetricDistanceWitness_prefix_independent_symmetric_zero_depth_collapse

theorem MetricDistanceWitness_prefix_independent_symmetric_zero_depth_continuation_splice
    {p q p' q' x y dxy dyx l r mid out : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) →
      MetricDistanceWitness (append p' y) (append x q') (append (append p' dyx) q') →
        MetricDistanceDepth dxy = 0 →
          Cont l dyx mid → Cont mid r out → Cont l r out := by
  intro forward reverse depthZero leftCont rightCont
  have reverseDepth :
      MetricDistanceDepth dyx = 0 :=
    (MetricDistanceWitness_prefix_independent_symmetric_zero_depth_collapse
      (p := p) (q := q) (p' := p') (q' := q') (x := x) (y := y)
      (dxy := dxy) (dyx := dyx) forward reverse depthZero).right.left
  have distanceEmpty : hsame dyx BHist.Empty :=
    MetricDistanceDepth_zero_iff_empty.mp reverseDepth
  cases distanceEmpty
  cases leftCont
  exact rightCont

end BEDC.Derived.MetricUp
