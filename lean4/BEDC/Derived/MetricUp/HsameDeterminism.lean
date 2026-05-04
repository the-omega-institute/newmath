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

theorem MetricDistanceWitness_hsame_target_deterministic {x x' y y' d d' : BHist} :
    hsame x x' -> hsame d d' -> MetricDistanceWitness x y d ->
      MetricDistanceWitness x' y' d' -> Cont x y d ∧ Cont x' y' d' ∧ hsame y y' := by
  intro sameSource sameDistance left right
  have leftCont : Cont x y d := left.2.2.2
  have rightCont : Cont x' y' d' := right.2.2.2
  constructor
  · exact leftCont
  · constructor
    · exact rightCont
    · cases sameSource
      cases sameDistance
      exact cont_left_cancel leftCont rightCont

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

theorem MetricDistanceWitness_visible_context_hsame_target_deterministic
    {p q p' q' x x' y y' d d' : BHist} :
    hsame x x' -> hsame d d' ->
      MetricDistanceWitness (append p x) (append y q) (append (append p d) q) ->
        MetricDistanceWitness (append p' x') (append y' q') (append (append p' d') q') ->
          hsame y y' := by
  intro sameSource sameDistance left right
  have leftCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := d)).mp left
  have rightCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p') (q := q') (x := x') (y := y')
      (d := d')).mp right
  have targetData :=
    MetricDistanceWitness_hsame_target_deterministic sameSource sameDistance leftCentral.2.2
      rightCentral.2.2
  exact targetData.2.2

theorem MetricDistanceWitness_visible_context_prefix_independent_endpoint_hsame_result_deterministic
    {p q p' q' x x' y y' d e : BHist} :
    hsame x x' -> hsame y y' ->
      MetricDistanceWitness (append p x) (append y q) (append (append p d) q) ->
        MetricDistanceWitness (append p' x') (append y' q') (append (append p' e) q') ->
          hsame d e := by
  intro sameX sameY left right
  have leftCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := d)).mp left
  have rightCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p') (q := q') (x := x') (y := y')
      (d := e)).mp right
  exact
    MetricDistanceWitness_hsame_result_deterministic sameX sameY leftCentral.2.2
      rightCentral.2.2

theorem MetricDistanceWitness_left_e1_result_tail_deterministic {x y d d' : BHist} :
    MetricDistanceWitness (BHist.e1 x) y (BHist.e1 d) ->
      MetricDistanceWitness (BHist.e1 x) y (BHist.e1 d') -> hsame d d' := by
  intro left right
  have visibleSame : hsame (BHist.e1 d) (BHist.e1 d') :=
    cont_deterministic left.2.2.2 right.2.2.2
  exact hsame_e1_iff.mp visibleSame

theorem MetricDistanceWitness_right_e1_result_tail_deterministic {x y d d' : BHist} :
    MetricDistanceWitness x (BHist.e1 y) (BHist.e1 d) ->
      MetricDistanceWitness x (BHist.e1 y) (BHist.e1 d') -> hsame d d' := by
  intro left right
  have visibleSame : hsame (BHist.e1 d) (BHist.e1 d') :=
    cont_deterministic left.2.2.2 right.2.2.2
  exact hsame_e1_iff.mp visibleSame

end BEDC.Derived.MetricUp
