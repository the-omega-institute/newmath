import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def MetricBallBudget (dist radius : BHist) : Prop :=
  MetricDistanceWitness dist BHist.Empty radius

theorem MetricBallBudget_composition {x y z dxy dyz dxz r s rs : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness x z dxz -> MetricBallBudget dxy r -> MetricBallBudget dyz s ->
        Cont r s rs -> hsame (append dxy dyz) dxz -> MetricBallBudget dxz rs := by
  intro xy yz xz budgetXY budgetYZ budgetSum sameComposite
  have composedCarrier : UnaryHistory (append dxy dyz) :=
    unary_append_closed xy.right.right.left yz.right.right.left
  have budgetXYData :=
    (MetricDistanceWitness_empty_right_iff (x := dxy) (d := r)).mp budgetXY
  have budgetYZData :=
    (MetricDistanceWitness_empty_right_iff (x := dyz) (d := s)).mp budgetYZ
  have sameRS : hsame rs dxz := by
    cases budgetXYData.right
    cases budgetYZData.right
    exact budgetSum.trans sameComposite
  exact
    (MetricDistanceWitness_empty_right_iff (x := dxz) (d := rs)).mpr
      (And.intro (unary_transport composedCarrier sameComposite) sameRS)

end BEDC.Derived.MetricUp
