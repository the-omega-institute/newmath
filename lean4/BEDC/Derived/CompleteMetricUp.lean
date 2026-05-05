import BEDC.Derived.MetricUp

namespace BEDC.Derived.CompleteMetricUp

open BEDC.FKernel.Hist
open BEDC.Derived.MetricUp

theorem SingletonCompleteMetric_laws :
    hsame BHist.Empty BHist.Empty ∧
      (forall {x : BHist}, hsame x BHist.Empty ->
        MetricDistanceWitness x BHist.Empty BHist.Empty) ∧
      (forall {x y : BHist}, hsame x BHist.Empty -> hsame y BHist.Empty -> hsame x y) := by
  constructor
  · exact hsame_refl BHist.Empty
  constructor
  · intro x sameX
    exact
      (MetricDistanceWitness_empty_distance_iff (x := x) (y := BHist.Empty)).mpr
        (And.intro sameX (hsame_refl BHist.Empty))
  · intro x y sameX sameY
    exact hsame_trans sameX (hsame_symm sameY)

end BEDC.Derived.CompleteMetricUp
