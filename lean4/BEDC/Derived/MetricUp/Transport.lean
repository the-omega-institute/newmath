import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem MetricDistanceWitness_cont_hsame_transport {x x' y y' d d' : BHist} :
    hsame x x' -> hsame y y' -> hsame d d' -> MetricDistanceWitness x y d ->
      Cont x' y' d' := by
  intro sameX sameY sameD witness
  cases sameX
  cases sameY
  cases sameD
  exact witness.right.right.right

end BEDC.Derived.MetricUp
