import BEDC.Derived.MetricUp
import BEDC.FKernel.Bundle

namespace BEDC.Derived.TotallyBoundedUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.Derived.MetricUp

theorem SingletonMetricTotallyBounded_laws :
    hsame BHist.Empty BHist.Empty ∧
      InBundle BHist.Empty (ProbeBundle.Bcons BHist.Empty ProbeBundle.Bnil) ∧
        (forall {x : BHist}, hsame x BHist.Empty ->
          MetricDistanceWitness x BHist.Empty BHist.Empty) ∧
          (forall {x y : BHist}, hsame x BHist.Empty -> hsame y BHist.Empty ->
            hsame x y) := by
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · exact inBundle_cons_self BHist.Empty ProbeBundle.Bnil
    · constructor
      · intro x sameX
        exact (MetricDistanceWitness_empty_distance_iff (x := x) (y := BHist.Empty)).mpr
          (And.intro sameX (hsame_refl BHist.Empty))
      · intro x y sameX sameY
        exact hsame_trans sameX (hsame_symm sameY)

end BEDC.Derived.TotallyBoundedUp
