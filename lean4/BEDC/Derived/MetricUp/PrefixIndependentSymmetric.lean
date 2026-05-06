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

theorem MetricDistanceWitness_prefix_independent_symmetric_zero_depth_witness_splice
    {p q p' q' x y dxy dyx l r mid out : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness (append p' y) (append x q') (append (append p' dyx) q') ->
        MetricDistanceDepth dxy = 0 -> UnaryHistory l -> UnaryHistory r ->
          Cont l dyx mid -> Cont mid r out -> MetricDistanceWitness l r out := by
  intro forward reverse depthZero lCarrier rCarrier leftCont rightCont
  have spliced : Cont l r out :=
    MetricDistanceWitness_prefix_independent_symmetric_zero_depth_continuation_splice
      forward reverse depthZero leftCont rightCont
  exact And.intro lCarrier
    (And.intro rCarrier (And.intro (unary_cont_closed lCarrier rCarrier spliced) spliced))

theorem MetricDistanceWitness_prefix_independent_symmetric_zero_depth_distance_continuation_result
    {p q p' q' x y dxy dyx l mid out : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness (append p' y) (append x q') (append (append p' dyx) q') ->
        MetricDistanceDepth dxy = 0 -> Cont l dxy mid -> Cont mid dyx out ->
          hsame out l := by
  intro forward reverse depthZero leftCont rightCont
  have collapse :=
    MetricDistanceWitness_prefix_independent_symmetric_zero_depth_collapse
      (p := p) (q := q) (p' := p') (q' := q') (x := x) (y := y)
      (dxy := dxy) (dyx := dyx) forward reverse depthZero
  have leftEmpty : hsame dxy BHist.Empty :=
    MetricDistanceDepth_zero_iff_empty.mp depthZero
  have rightEmpty : hsame dyx BHist.Empty :=
    MetricDistanceDepth_zero_iff_empty.mp collapse.right.left
  cases leftEmpty
  cases rightEmpty
  cases leftCont
  cases rightCont
  rfl

theorem MetricDistanceWitness_prefix_independent_symmetric_zero_depth_reverse_empty_boundary_package
    {p q p' q' x y dxy dyx : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness (append p' y) (append x q') (append (append p' dyx) q') ->
        MetricDistanceDepth dxy = 0 -> MetricDistanceDepth dyx = 0 ∧
          MetricDistanceWitness (append p' BHist.Empty) (append BHist.Empty q')
            (append (append p' BHist.Empty) q') ∧ hsame x BHist.Empty ∧
              hsame y BHist.Empty := by
  intro forward reverse depthZero
  have collapse :=
    MetricDistanceWitness_prefix_independent_symmetric_zero_depth_collapse
      (p := p) (q := q) (p' := p') (q' := q') (x := x) (y := y)
      (dxy := dxy) (dyx := dyx) forward reverse depthZero
  have reverseCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p') (q := q') (x := y) (y := x)
      (d := dyx)).mp reverse
  have reverseEmpty :
      MetricDistanceWitness (append p' BHist.Empty) (append BHist.Empty q')
        (append (append p' BHist.Empty) q') :=
    (MetricDistanceWitness_visible_context_empty_distance_iff (p := p') (q := q')
      (x := BHist.Empty) (y := BHist.Empty)).mpr
      ⟨reverseCentral.1, reverseCentral.2.1, hsame_refl BHist.Empty, hsame_refl BHist.Empty⟩
  exact ⟨collapse.2.1, reverseEmpty, collapse.2.2.1, collapse.2.2.2⟩

theorem MetricDistanceWitness_prefix_independent_symmetric_zero_depth_two_sided_empty_boundary_package
    {p q p' q' x y dxy dyx : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness (append p' y) (append x q') (append (append p' dyx) q') ->
        MetricDistanceDepth dxy = 0 ->
          MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
              (append (append p BHist.Empty) q) ∧
            MetricDistanceWitness (append p' BHist.Empty) (append BHist.Empty q')
              (append (append p' BHist.Empty) q') ∧
              MetricDistanceDepth dyx = 0 ∧ hsame x BHist.Empty ∧ hsame y BHist.Empty := by
  intro forward reverse depthZero
  have collapse :=
    MetricDistanceWitness_prefix_independent_symmetric_zero_depth_collapse
      (p := p) (q := q) (p' := p') (q' := q') (x := x) (y := y)
      (dxy := dxy) (dyx := dyx) forward reverse depthZero
  have forwardCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := dxy)).mp forward
  have forwardEmpty :
      MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
        (append (append p BHist.Empty) q) :=
    (MetricDistanceWitness_visible_context_empty_distance_iff (p := p) (q := q)
      (x := BHist.Empty) (y := BHist.Empty)).mpr
      ⟨forwardCentral.1, forwardCentral.2.1, hsame_refl BHist.Empty,
        hsame_refl BHist.Empty⟩
  have reversePackage :=
    MetricDistanceWitness_prefix_independent_symmetric_zero_depth_reverse_empty_boundary_package
      (p := p) (q := q) (p' := p') (q' := q') (x := x) (y := y)
      (dxy := dxy) (dyx := dyx) forward reverse depthZero
  exact
    ⟨forwardEmpty, reversePackage.2.1, reversePackage.1, collapse.2.2.1, collapse.2.2.2⟩

theorem MetricDistanceWitness_prefix_independent_symmetric_zero_depth_reverse_distance_continuation_result
    {p q p' q' x y dxy dyx l mid out : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness (append p' y) (append x q') (append (append p' dyx) q') ->
        MetricDistanceDepth dxy = 0 -> Cont l dyx mid -> Cont mid dxy out ->
          hsame out l := by
  intro forward reverse depthZero leftCont rightCont
  have collapse :=
    MetricDistanceWitness_prefix_independent_symmetric_zero_depth_collapse
      (p := p) (q := q) (p' := p') (q' := q') (x := x) (y := y)
      (dxy := dxy) (dyx := dyx) forward reverse depthZero
  exact
    MetricDistanceWitness_prefix_independent_symmetric_zero_depth_distance_continuation_result
      (p := p') (q := q') (p' := p) (q' := q) (x := y) (y := x)
      (dxy := dyx) (dyx := dxy) reverse forward collapse.right.left leftCont rightCont

end BEDC.Derived.MetricUp
