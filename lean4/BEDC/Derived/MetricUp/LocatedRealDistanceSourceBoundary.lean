import BEDC.Derived.MetricUp.PublicDistanceSurface

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_locatedreal_distance_source_boundary
    {p q x y d budget provenance visible : BHist} :
    UnaryHistory p ->
      UnaryHistory q ->
        MetricspacePublicDistanceSurface x y d budget provenance ->
          MetricDistanceWitness (append p x) (append y q) visible ->
            hsame visible (append (append p d) q) ->
              MetricDistanceWitness x y d ∧ UnaryHistory provenance ∧
                Cont d budget provenance ∧ hsame provenance (append d budget) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro pUnary qUnary surface visibleWitness sameVisible
  have visibleRows :=
    MetricspacePublicDistanceSurface_visible_context_consumer_surface
      pUnary qUnary surface visibleWitness sameVisible
  have centralRows :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := d)).mp visibleRows.left
  exact
    And.intro centralRows.right.right
      (And.intro visibleRows.right.left
        (And.intro visibleRows.right.right.left visibleRows.right.right.right))

end BEDC.Derived.MetricUp
