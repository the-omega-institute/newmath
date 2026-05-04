import BEDC.Derived.MetricUp
import BEDC.Derived.MetricUp.DepthClassifier

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

theorem MetricDistanceWitness_nonempty_distance_endpoint_positive_depth {x y d : BHist} :
    MetricDistanceWitness x y d -> (hsame d BHist.Empty -> False) ->
      (0 < MetricDistanceDepth x) ∨ (0 < MetricDistanceDepth y) := by
  intro witness nonemptyDistance
  have endpointNonempty :=
    MetricDistanceWitness_nonempty_distance_endpoint_nonempty witness nonemptyDistance
  cases endpointNonempty with
  | inl xNonempty =>
      exact Or.inl ((MetricDistanceDepth_positive_iff_nonempty (d := x)).mpr xNonempty)
  | inr yNonempty =>
      exact Or.inr ((MetricDistanceDepth_positive_iff_nonempty (d := y)).mpr yNonempty)

theorem MetricDistanceWitness_nonempty_distance_endpoint_e1_cases {x y d : BHist} :
    MetricDistanceWitness x y d -> (hsame d BHist.Empty -> False) ->
      (∃ x0 : BHist, x = BHist.e1 x0 ∧ UnaryHistory x0) ∨
        (∃ y0 : BHist, y = BHist.e1 y0 ∧ UnaryHistory y0) := by
  intro witness nonemptyDistance
  have endpointNonempty :=
    MetricDistanceWitness_nonempty_distance_endpoint_nonempty witness nonemptyDistance
  cases endpointNonempty with
  | inl xNonempty =>
      exact Or.inl (unary_history_nonempty_e1_tail witness.left xNonempty)
  | inr yNonempty =>
      exact Or.inr (unary_history_nonempty_e1_tail witness.right.left yNonempty)

theorem MetricDistanceWitness_empty_source_nonempty_distance_target_e1_cases {target dist : BHist} :
    MetricDistanceWitness BHist.Empty target dist -> (hsame dist BHist.Empty -> False) ->
      ∃ targetTail : BHist, target = BHist.e1 targetTail ∧ UnaryHistory targetTail := by
  intro witness nonemptyDistance
  have endpointCases :=
    MetricDistanceWitness_nonempty_distance_endpoint_e1_cases witness nonemptyDistance
  cases endpointCases with
  | inl sourceCase =>
      cases sourceCase with
      | intro sourceTail sourceData =>
          cases sourceData.left
  | inr targetCase =>
      exact targetCase

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

theorem MetricDistanceWitness_empty_distance_visible_endpoint_absurd
    {x y d tx ty : BHist} :
    MetricDistanceWitness x y d -> hsame d BHist.Empty ->
      (hsame x (BHist.e1 tx) -> False) ∧ (hsame y (BHist.e1 ty) -> False) := by
  intro witness sameD
  have emptyWitness : MetricDistanceWitness x y BHist.Empty :=
    And.intro witness.left
      (And.intro witness.right.left
        (And.intro unary_empty
          (cont_result_hsame_transport witness.right.right.right sameD)))
  have endpoints := (MetricDistanceWitness_empty_distance_iff (x := x) (y := y)).mp
    emptyWitness
  constructor
  · intro sameVisible
    exact not_hsame_emp_e1 (hsame_trans (hsame_symm endpoints.left) sameVisible)
  · intro sameVisible
    exact not_hsame_emp_e1 (hsame_trans (hsame_symm endpoints.right) sameVisible)

theorem MetricDistanceWitness_e1_pair_empty_distance_absurd {x y : BHist} :
    MetricDistanceWitness (BHist.e1 x) (BHist.e1 y) BHist.Empty -> False := by
  intro witness
  have endpoints :=
    (MetricDistanceWitness_empty_distance_iff (x := BHist.e1 x) (y := BHist.e1 y)).mp
      witness
  exact not_hsame_e1_empty endpoints.left

theorem MetricDistanceWitness_right_boundary_visible_context_distance_source {p q x d : BHist} :
    MetricDistanceWitness (append p x) (append BHist.Empty q) (append (append p d) q) ->
      hsame d x ∧ MetricDistanceDepth d = MetricDistanceDepth x := by
  intro visible
  have boundary :=
    (MetricDistanceWitness_right_boundary_visible_context_iff
      (p := p) (q := q) (x := x) (d := d)).mp visible
  constructor
  · exact boundary.right.right.right
  · cases boundary.right.right.right
    rfl

theorem MetricDistanceWitness_left_boundary_visible_context_distance_target {p q y d : BHist} :
    MetricDistanceWitness (append p BHist.Empty) (append y q) (append (append p d) q) ->
      hsame d y ∧ MetricDistanceDepth d = MetricDistanceDepth y := by
  intro visible
  have boundary :=
    (MetricDistanceWitness_left_boundary_visible_context_iff
      (p := p) (q := q) (y := y) (d := d)).mp visible
  constructor
  · exact boundary.right.right.right
  · cases boundary.right.right.right
    rfl

end BEDC.Derived.MetricUp
