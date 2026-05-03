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

end BEDC.Derived.MetricUp
