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

end BEDC.Derived.MetricUp
