import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_empty_source_e1_distance_target_exactness {target d : BHist} :
    MetricDistanceWitness BHist.Empty target (BHist.e1 d) ->
      target = BHist.e1 d /\ UnaryHistory d := by
  intro witness
  have boundary :=
    (MetricDistanceWitness_empty_left_iff (y := target) (d := BHist.e1 d)).mp witness
  have targetShape := hsame_e1_inversion boundary.right
  cases targetShape with
  | intro k data =>
      cases data with
      | intro targetEq sameDK =>
          cases sameDK
          cases targetEq
          exact And.intro rfl (unary_e1_inversion boundary.left)

theorem MetricDistanceWitness_nonempty_distance_endpoint_nonempty {x y d : BHist} :
    MetricDistanceWitness x y d -> (hsame d BHist.Empty -> False) ->
      (hsame x BHist.Empty -> False) \/ (hsame y BHist.Empty -> False) := by
  intro witness nonemptyDistance
  cases x with
  | Empty =>
      cases y with
      | Empty =>
          have distanceEmpty : hsame d BHist.Empty :=
            cont_left_unit_result witness.right.right.right
          exact False.elim (nonemptyDistance distanceEmpty)
      | e0 y0 =>
          exact Or.inr (fun sameY => not_hsame_e0_empty sameY)
      | e1 y1 =>
          exact Or.inr (fun sameY => not_hsame_e1_empty sameY)
  | e0 x0 =>
      exact Or.inl (fun sameX => not_hsame_e0_empty sameX)
  | e1 x1 =>
      exact Or.inl (fun sameX => not_hsame_e1_empty sameX)

theorem MetricDistanceWitness_e0_component_absurd {x y d : BHist} :
    (MetricDistanceWitness (BHist.e0 x) y d -> False) ∧
      (MetricDistanceWitness x (BHist.e0 y) d -> False) ∧
        (MetricDistanceWitness x y (BHist.e0 d) -> False) := by
  constructor
  · intro witness
    exact unary_no_zero_extension witness.left
  · constructor
    · intro witness
      exact unary_no_zero_extension witness.right.left
    · intro witness
      exact unary_no_zero_extension witness.right.right.left

theorem MetricDistanceWitness_e1_pair_empty_distance_absurd {x y : BHist} :
    MetricDistanceWitness (BHist.e1 x) (BHist.e1 y) BHist.Empty -> False := by
  intro witness
  have endpoints :=
    (MetricDistanceWitness_empty_distance_iff (x := BHist.e1 x) (y := BHist.e1 y)).mp
      witness
  exact not_hsame_e1_empty endpoints.left

end BEDC.Derived.MetricUp
