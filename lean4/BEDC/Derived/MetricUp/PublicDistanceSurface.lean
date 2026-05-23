import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def MetricspacePublicDistanceSurface (x y d budget provenance : BHist) : Prop :=
  MetricDistanceWitness x y d ∧ UnaryHistory budget ∧ Cont d budget provenance

def MetricLedgerPolicy (x y d budget provenance : BHist) : Prop :=
  MetricspacePublicDistanceSurface x y d budget provenance ∧
    hsame provenance (append d budget)

theorem MetricLedgerPolicy_rows {x y d budget provenance : BHist} :
    MetricLedgerPolicy x y d budget provenance ->
      MetricDistanceWitness x y d ∧ UnaryHistory budget ∧ Cont d budget provenance ∧
        hsame provenance (append d budget) := by
  intro policy
  exact And.intro policy.left.left
    (And.intro policy.left.right.left (And.intro policy.left.right.right policy.right))

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

theorem MetricspacePublicDistanceSurface_hsame_transport
    {x x' y y' d d' budget budget' provenance provenance' : BHist} :
    MetricspacePublicDistanceSurface x y d budget provenance ->
      hsame x x' ->
        hsame y y' ->
          hsame d d' ->
            hsame budget budget' ->
              hsame provenance provenance' ->
                MetricspacePublicDistanceSurface x' y' d' budget' provenance' ∧
                  Cont d' budget' provenance' := by
  intro surface sameX sameY sameD sameBudget sameProvenance
  cases sameX
  cases sameY
  cases sameD
  cases sameBudget
  cases sameProvenance
  exact And.intro surface surface.right.right

end BEDC.Derived.MetricUp
