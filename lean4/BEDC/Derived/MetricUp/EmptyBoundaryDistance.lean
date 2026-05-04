import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

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

end BEDC.Derived.MetricUp
