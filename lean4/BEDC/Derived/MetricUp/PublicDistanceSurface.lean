import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def MetricspacePublicDistanceSurface (x y d budget provenance : BHist) : Prop :=
  MetricDistanceWitness x y d ∧ UnaryHistory budget ∧ Cont d budget provenance

theorem MetricspacePublicDistanceSurface_exhaustion {x y d budget provenance : BHist} :
    MetricspacePublicDistanceSurface x y d budget provenance ->
      UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory d ∧ UnaryHistory budget ∧
        UnaryHistory provenance ∧ MetricDistanceWitness x y d ∧
          Cont d budget provenance ∧ hsame provenance (append d budget) := by
  intro surface
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed surface.left.right.right.left surface.right.left surface.right.right
  exact And.intro surface.left.left
    (And.intro surface.left.right.left
      (And.intro surface.left.right.right.left
        (And.intro surface.right.left
          (And.intro provenanceUnary
            (And.intro surface.left
              (And.intro surface.right.right surface.right.right))))))

theorem MetricspacePublicDistanceSurface_visible_context_consumer_surface
    {p q x y d budget provenance visible : BHist} :
    UnaryHistory p ->
      UnaryHistory q ->
        MetricspacePublicDistanceSurface x y d budget provenance ->
          MetricDistanceWitness (append p x) (append y q) visible ->
            hsame visible (append (append p d) q) ->
              MetricDistanceWitness (append p x) (append y q) (append (append p d) q) ∧
                UnaryHistory provenance ∧ Cont d budget provenance ∧
                  hsame provenance (append d budget) := by
  intro _pCarrier _qCarrier surface visibleWitness sameVisible
  have publicRows := MetricspacePublicDistanceSurface_exhaustion surface
  have transportedVisible :
      MetricDistanceWitness (append p x) (append y q) (append (append p d) q) := by
    cases sameVisible
    exact visibleWitness
  exact And.intro transportedVisible
    (And.intro publicRows.right.right.right.right.left
      (And.intro publicRows.right.right.right.right.right.right.left
        publicRows.right.right.right.right.right.right.right))

end BEDC.Derived.MetricUp
