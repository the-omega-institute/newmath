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

theorem MetricDistanceWitness_visible_context_hsame_source_deterministic
    {p q p' q' x x' y y' d d' : BHist} :
    hsame y y' -> hsame d d' ->
      MetricDistanceWitness (append p x) (append y q) (append (append p d) q) ->
        MetricDistanceWitness (append p' x') (append y' q') (append (append p' d') q') ->
          hsame x x' := by
  intro sameTarget sameDistance left right
  have leftCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := d)).mp left
  have rightCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p') (q := q') (x := x') (y := y')
      (d := d')).mp right
  have sourceData :=
    MetricDistanceWitness_hsame_source_deterministic sameTarget sameDistance leftCentral.2.2
      rightCentral.2.2
  exact sourceData.2.2

end BEDC.Derived.MetricUp
