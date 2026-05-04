import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem MetricDistanceWitness_hsame_source_deterministic {x x' y y' d d' : BHist} :
    hsame y y' -> hsame d d' -> MetricDistanceWitness x y d ->
      MetricDistanceWitness x' y' d' -> Cont x y d ∧ Cont x' y' d' ∧ hsame x x' := by
  intro sameTarget sameDistance left right
  have leftCont : Cont x y d := left.2.2.2
  have rightCont : Cont x' y' d' := right.2.2.2
  constructor
  · exact leftCont
  · constructor
    · exact rightCont
    · cases sameTarget
      cases sameDistance
      exact cont_right_cancel leftCont rightCont

end BEDC.Derived.MetricUp
