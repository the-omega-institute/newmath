import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_visible_context_determinacy {p q x y d e : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p d) q) ->
      MetricDistanceWitness (append p x) (append y q) (append (append p e) q) ->
        hsame d e := by
  intro leftVisible rightVisible
  have leftData :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := d)).mp leftVisible
  have rightData :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := e)).mp rightVisible
  cases leftData with
  | intro _leftPrefix leftRest =>
      cases leftRest with
      | intro _leftSuffix leftCentral =>
          cases rightData with
          | intro _rightPrefix rightRest =>
              cases rightRest with
              | intro _rightSuffix rightCentral =>
                  exact cont_deterministic leftCentral.2.2.2 rightCentral.2.2.2

end BEDC.Derived.MetricUp
