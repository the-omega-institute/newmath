import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetricspaceOpenPhaseConsumerInterface {p q x y d consumer : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p d) q) →
      Cont d consumer BHist.Empty →
        UnaryHistory p ∧ UnaryHistory q ∧ hsame x BHist.Empty ∧
          hsame y BHist.Empty ∧ hsame consumer BHist.Empty := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro visible consumerRoute
  have consumerBoundary := cont_empty_result_inversion consumerRoute
  cases consumerBoundary.left
  have emptyVisible :
      MetricDistanceWitness (append p x) (append y q)
        (append (append p BHist.Empty) q) := visible
  have context :=
    (MetricDistanceWitness_visible_context_empty_distance_iff (p := p) (q := q)
      (x := x) (y := y)).mp emptyVisible
  exact
    ⟨context.left, context.right.left, context.right.right.left,
      context.right.right.right, consumerBoundary.right⟩

theorem MetricspaceApartnessPositiveDistanceTriangleBoundary
    {p q x y z dxy dyz dxz : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) →
      MetricDistanceWitness (append p y) (append z q) (append (append p dyz) q) →
        MetricDistanceWitness (append p x) (append z q) (append (append p dxz) q) →
          UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory x ∧ UnaryHistory y ∧
            UnaryHistory z ∧ UnaryHistory dxy ∧ UnaryHistory dyz ∧ UnaryHistory dxz := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro xy yz xz
  have xyContext :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := dxy)).mp xy
  have yzContext :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := y) (y := z)
      (d := dyz)).mp yz
  have xzContext :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := z)
      (d := dxz)).mp xz
  exact
    ⟨xyContext.left, xyContext.right.left, xyContext.right.right.left,
      xyContext.right.right.right.left, yzContext.right.right.right.left,
      xyContext.right.right.right.right.left, yzContext.right.right.right.right.left,
      xzContext.right.right.right.right.left⟩

end BEDC.Derived.MetricUp
