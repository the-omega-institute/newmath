import BEDC.Derived.MetricUp.PublicDistanceSurface
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MetricSeedClosureSurface_public_package {p q x y d budget provenance : BHist} :
    UnaryHistory p -> UnaryHistory q ->
      MetricspacePublicDistanceSurface x y d budget provenance ->
        MetricDistanceWitness (append p x) (append y q) (append (append p d) q) ∧
          SemanticNameCert (MetricDistanceWitness (append p x) (append y q))
            (MetricDistanceWitness (append p x) (append y q))
            (MetricDistanceWitness (append p x) (append y q)) hsame ∧
          UnaryHistory provenance ∧ Cont d budget provenance ∧
            hsame provenance (append d budget) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro pCarrier qCarrier surface
  have rows := MetricspacePublicDistanceSurface_exhaustion surface
  have visible :
      MetricDistanceWitness (append p x) (append y q) (append (append p d) q) :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := d)).mpr
      (And.intro pCarrier (And.intro qCarrier rows.right.right.right.right.right.left))
  exact And.intro visible
    (And.intro
      (MetricDistanceWitness_semanticNameCert
        (unary_append_closed pCarrier rows.left)
        (unary_append_closed rows.right.left qCarrier))
      (And.intro rows.right.right.right.right.left
        (And.intro rows.right.right.right.right.right.right.left
          rows.right.right.right.right.right.right.right)))

theorem MetricSeedClosureSurface_transport_boundary_package {p q x y d d' : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p d) q) ->
      hsame d d' ->
        MetricDistanceWitness (append p x) (append y q) (append (append p d') q) ->
          UnaryHistory p ∧ UnaryHistory q ∧
            hsame (append (append p d) q) (append (append p d') q) ∧
            MetricDistanceWitness x y d ∧ MetricDistanceWitness x y d' := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory MetricDistanceWitness
  intro left sameDistance right
  have leftRows :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := d)).mp left
  have rightRows :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := d')).mp right
  have sameVisible :
      hsame (append (append p d) q) (append (append p d') q) := by
    cases sameDistance
    rfl
  exact And.intro leftRows.left
    (And.intro leftRows.right.left
      (And.intro sameVisible
        (And.intro leftRows.right.right rightRows.right.right)))

end BEDC.Derived.MetricUp
