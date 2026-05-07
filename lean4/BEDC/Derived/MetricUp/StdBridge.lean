import BEDC.Derived.MetricUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MetricUp_StdBridge {x y d : BHist} :
    UnaryHistory x ->
      UnaryHistory y ->
        MetricDistanceWitness x y d ->
          MetricDistanceWitness x y (append x y) ∧
            SemanticNameCert (MetricDistanceWitness x y) (MetricDistanceWitness x y)
              (MetricDistanceWitness x y) hsame ∧
                hsame d (append x y) := by
  intro xCarrier yCarrier witness
  exact And.intro
    (And.intro xCarrier
      (And.intro yCarrier
        (And.intro (unary_append_closed xCarrier yCarrier) (cont_intro rfl))))
    (And.intro (MetricDistanceWitness_semanticNameCert xCarrier yCarrier)
      (cont_deterministic witness.2.2.2 (cont_intro rfl)))

theorem MetricDistanceWitness_standard_boundary_bridge {p q y d : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append y q) (append (append p d) q) ->
      SemanticNameCert (MetricDistanceWitness (append p BHist.Empty) (append y q))
        (MetricDistanceWitness (append p BHist.Empty) (append y q))
        (MetricDistanceWitness (append p BHist.Empty) (append y q)) hsame ∧
        UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory y ∧ hsame d y := by
  intro visible
  have boundary :=
    (MetricDistanceWitness_left_boundary_visible_context_iff (p := p) (q := q)
      (y := y) (d := d)).mp visible
  have sourceCarrier : UnaryHistory (append p BHist.Empty) :=
    unary_append_closed boundary.left unary_empty
  have targetCarrier : UnaryHistory (append y q) :=
    unary_append_closed boundary.right.right.left boundary.right.left
  exact And.intro (MetricDistanceWitness_semanticNameCert sourceCarrier targetCarrier) boundary

end BEDC.Derived.MetricUp
