import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_visible_context_empty_distance_continuation_splice
    {p q x y l r mid out : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p BHist.Empty) q) ->
      Cont l x mid -> Cont mid r out -> Cont l r out := by
  intro visible leftCont rightCont
  have endpoints :=
    (MetricDistanceWitness_visible_context_empty_distance_iff (p := p) (q := q)
      (x := x) (y := y)).mp visible
  cases endpoints.right.right.left
  cases leftCont
  exact rightCont

theorem MetricDistanceWitness_visible_context_empty_distance_continuation_splice_hsame
    {p q x y l r mid out out' : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p BHist.Empty) q) ->
      Cont l x mid -> Cont mid r out -> Cont l r out' -> hsame out out' := by
  intro visible leftCont rightCont displayed
  have spliced : Cont l r out :=
    MetricDistanceWitness_visible_context_empty_distance_continuation_splice visible leftCont
      rightCont
  exact cont_deterministic spliced displayed

theorem MetricDistanceWitness_visible_context_empty_distance_append_unit_laws
    {p q x y l r : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p BHist.Empty) q) ->
      append x r = r ∧ append l y = l := by
  intro visible
  have endpoints :=
    (MetricDistanceWitness_visible_context_empty_distance_iff (p := p) (q := q)
      (x := x) (y := y)).mp visible
  cases endpoints.right.right.left
  cases endpoints.right.right.right
  exact And.intro (append_empty_left r) (append_empty_right l)

theorem MetricDistanceWitness_visible_context_empty_distance_witness_splice
    {p q x y l r mid out : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p BHist.Empty) q) ->
      UnaryHistory l -> UnaryHistory r -> Cont l x mid -> Cont mid r out ->
        MetricDistanceWitness l r out := by
  intro visible lCarrier rCarrier leftCont rightCont
  have spliced : Cont l r out :=
    MetricDistanceWitness_visible_context_empty_distance_continuation_splice visible leftCont
      rightCont
  exact And.intro lCarrier
    (And.intro rCarrier (And.intro (unary_cont_closed lCarrier rCarrier spliced) spliced))

theorem MetricDistanceWitness_visible_context_empty_distance_continuation_witness_depth
    {p q x y l r mid out : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p BHist.Empty) q) ->
      UnaryHistory l -> UnaryHistory r -> Cont l x mid -> Cont mid r out ->
        MetricDistanceWitness l r out ∧
          MetricDistanceDepth out = MetricDistanceDepth l + MetricDistanceDepth r := by
  intro visible lCarrier rCarrier leftCont rightCont
  have witness : MetricDistanceWitness l r out :=
    MetricDistanceWitness_visible_context_empty_distance_witness_splice visible lCarrier rCarrier
      leftCont rightCont
  exact And.intro witness (MetricDistanceWitness_depth_add witness)

theorem MetricDistanceWitness_empty_boundary_visible_context_distance_empty {p q d : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
      (append (append p d) q) -> hsame d BHist.Empty ∧ MetricDistanceDepth d = 0 := by
  intro visible
  have visibleData :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := BHist.Empty)
      (y := BHist.Empty) (d := d)).mp visible
  have central : MetricDistanceWitness BHist.Empty BHist.Empty d := visibleData.2.2
  have boundary :=
    (MetricDistanceWitness_empty_left_iff (y := BHist.Empty) (d := d)).mp central
  constructor
  · exact boundary.right
  · cases boundary.right
    rfl

theorem MetricDistanceWitness_empty_boundary_visible_context_append_unit_laws
    {p q d l r : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
      (append (append p d) q) -> append d r = r ∧ append l d = l := by
  intro visible
  have distanceEmpty :
      hsame d BHist.Empty :=
    (MetricDistanceWitness_empty_boundary_visible_context_distance_empty
      (p := p) (q := q) (d := d) visible).left
  cases distanceEmpty
  exact And.intro (append_empty_left r) (append_empty_right l)

theorem MetricDistanceWitness_empty_boundary_visible_context_continuation_left_unit_result
    {p q d r out : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
      (append (append p d) q) → Cont d r out → hsame out r := by
  intro visible continuation
  have distanceEmpty :
      hsame d BHist.Empty :=
    (MetricDistanceWitness_empty_boundary_visible_context_distance_empty
      (p := p) (q := q) (d := d) visible).left
  cases distanceEmpty
  exact cont_left_unit_result continuation

theorem MetricDistanceWitness_empty_boundary_visible_context_left_unit_witness
    {p q d r out : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
      (append (append p d) q) -> UnaryHistory r -> Cont d r out ->
        MetricDistanceWitness BHist.Empty r out := by
  intro visible rCarrier continuation
  have distanceEmpty :
      hsame d BHist.Empty :=
    (MetricDistanceWitness_empty_boundary_visible_context_distance_empty
      (p := p) (q := q) (d := d) visible).left
  cases distanceEmpty
  exact And.intro unary_empty
    (And.intro rCarrier
      (And.intro (unary_cont_closed unary_empty rCarrier continuation) continuation))

theorem MetricDistanceWitness_empty_boundary_visible_context_right_unit_witness
    {p q d l out : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
      (append (append p d) q) -> UnaryHistory l -> Cont l d out ->
        MetricDistanceWitness l BHist.Empty out := by
  intro visible lCarrier continuation
  have distanceEmpty :
      hsame d BHist.Empty :=
    (MetricDistanceWitness_empty_boundary_visible_context_distance_empty
      (p := p) (q := q) (d := d) visible).left
  cases distanceEmpty
  exact And.intro lCarrier
    (And.intro unary_empty
      (And.intro (unary_cont_closed lCarrier unary_empty continuation) continuation))

theorem MetricDistanceWitness_empty_boundary_visible_context_continuation_left_unit_iff
    {p q d r out : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
      (append (append p d) q) → (Cont d r out ↔ hsame out r) := by
  intro visible
  have distanceEmpty :
      hsame d BHist.Empty :=
    (MetricDistanceWitness_empty_boundary_visible_context_distance_empty
      (p := p) (q := q) (d := d) visible).left
  cases distanceEmpty
  exact cont_left_unit_iff

theorem MetricDistanceWitness_empty_boundary_visible_context_continuation_right_unit_iff
    {p q d l out : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
      (append (append p d) q) → (Cont l d out ↔ hsame out l) := by
  intro visible
  have distanceEmpty :
      hsame d BHist.Empty :=
    (MetricDistanceWitness_empty_boundary_visible_context_distance_empty
      (p := p) (q := q) (d := d) visible).left
  cases distanceEmpty
  exact cont_right_unit_iff

theorem MetricDistanceWitness_empty_boundary_visible_context_continuation_splice
    {p q d l r mid out : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
      (append (append p d) q) →
        Cont l d mid → Cont mid r out → Cont l r out := by
  intro visible leftCont rightCont
  have distanceEmpty :
      hsame d BHist.Empty :=
    (MetricDistanceWitness_empty_boundary_visible_context_distance_empty
      (p := p) (q := q) (d := d) visible).left
  cases distanceEmpty
  cases leftCont
  exact rightCont

theorem MetricDistanceWitness_empty_boundary_visible_context_continuation_splice_hsame
    {p q d l r mid out out' : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
      (append (append p d) q) -> Cont l d mid -> Cont mid r out ->
        Cont l r out' -> hsame out out' := by
  intro visible leftCont rightCont displayed
  have spliced : Cont l r out :=
    MetricDistanceWitness_empty_boundary_visible_context_continuation_splice visible leftCont
      rightCont
  exact cont_deterministic spliced displayed

theorem MetricDistanceWitness_empty_boundary_visible_context_continuation_depth_add
    {p q d l r mid out : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
      (append (append p d) q) ->
      UnaryHistory l -> UnaryHistory r -> Cont l d mid -> Cont mid r out ->
        MetricDistanceDepth out = MetricDistanceDepth l + MetricDistanceDepth r := by
  intro visible lCarrier rCarrier leftCont rightCont
  have spliced : Cont l r out :=
    MetricDistanceWitness_empty_boundary_visible_context_continuation_splice visible leftCont
      rightCont
  have witness : MetricDistanceWitness l r out :=
    And.intro lCarrier
      (And.intro rCarrier (And.intro (unary_cont_closed lCarrier rCarrier spliced) spliced))
  exact MetricDistanceWitness_depth_add witness

theorem MetricDistanceWitness_empty_boundary_visible_context_unit_splice_commute
    {p q d l r outL outR : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
      (append (append p d) q) ->
      Cont l d outL -> Cont d r outR -> hsame (append outL r) (append l outR) := by
  intro visible leftCont rightCont
  have distanceEmpty :
      hsame d BHist.Empty :=
    (MetricDistanceWitness_empty_boundary_visible_context_distance_empty
      (p := p) (q := q) (d := d) visible).left
  cases distanceEmpty
  have sameLeft : hsame outL l := Iff.mp cont_right_unit_iff leftCont
  have sameRight : hsame outR r := cont_left_unit_result rightCont
  cases sameLeft
  cases sameRight
  rfl

theorem MetricDistanceWitness_empty_boundary_visible_context_witness_splice
    {p q d l r mid out : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append BHist.Empty q)
      (append (append p d) q) ->
      UnaryHistory l -> UnaryHistory r -> Cont l d mid -> Cont mid r out ->
        MetricDistanceWitness l r out := by
  intro visible lCarrier rCarrier leftCont rightCont
  have spliced : Cont l r out :=
    MetricDistanceWitness_empty_boundary_visible_context_continuation_splice visible leftCont
      rightCont
  exact And.intro lCarrier
    (And.intro rCarrier (And.intro (unary_cont_closed lCarrier rCarrier spliced) spliced))

end BEDC.Derived.MetricUp
