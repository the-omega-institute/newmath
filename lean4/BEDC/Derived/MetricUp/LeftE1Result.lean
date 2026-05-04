import BEDC.Derived.MetricUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_left_e1_result_shape {x y d : BHist} :
    MetricDistanceWitness (BHist.e1 x) y d ->
      exists k : BHist, hsame d (BHist.e1 k) ∧
        ((y = BHist.Empty ∧ UnaryHistory x ∧ hsame x k) ∨
          exists y1 : BHist,
            y = BHist.e1 y1 ∧ MetricDistanceWitness (BHist.e1 x) y1 k) := by
  intro witness
  cases d with
  | Empty =>
      cases witness with
      | intro _sourceCarrier rest =>
          cases rest with
          | intro _targetCarrier rest =>
              cases rest with
              | intro _distanceCarrier distance =>
                  cases y with
                  | Empty =>
                      cases distance
                  | e0 y0 =>
                      cases distance
                  | e1 y1 =>
                      cases distance
  | e0 d0 =>
      cases witness with
      | intro _sourceCarrier rest =>
          cases rest with
          | intro _targetCarrier rest =>
              cases rest with
              | intro distanceCarrier _distance =>
                  exact False.elim (unary_no_zero_extension distanceCarrier)
  | e1 k =>
      exact Exists.intro k
        (And.intro (hsame_refl (BHist.e1 k))
          (MetricDistanceWitness_left_e1_result_cases witness))

theorem MetricDistanceWitness_left_e1_result_iff {x y d : BHist} :
    MetricDistanceWitness (BHist.e1 x) y (BHist.e1 d) ↔
      (y = BHist.Empty ∧ UnaryHistory x ∧ hsame x d) ∨
        (∃ y1 : BHist, y = BHist.e1 y1 ∧ MetricDistanceWitness (BHist.e1 x) y1 d) := by
  constructor
  · intro witness
    exact MetricDistanceWitness_left_e1_result_cases witness
  · intro casesResult
    cases casesResult with
    | inl emptyCase =>
        cases emptyCase with
        | intro yEmpty data =>
            cases data with
            | intro xCarrier sameXD =>
                cases yEmpty
                exact
                  And.intro (unary_e1_closed xCarrier)
                    (And.intro unary_empty
                      (And.intro
                        (unary_e1_closed (unary_transport xCarrier sameXD))
                        (cont_right_unit_iff.mpr
                          (hsame_e1_congr (hsame_symm sameXD)))))
    | inr visibleCase =>
        cases visibleCase with
        | intro y1 data =>
            cases data with
            | intro yEq tailWitness =>
                cases yEq
                exact
                  And.intro tailWitness.left
                    (And.intro (unary_e1_closed tailWitness.right.left)
                      (And.intro (unary_e1_closed tailWitness.right.right.left)
                        (cont_step_one tailWitness.right.right.right)))

theorem MetricDistanceWitness_left_e1_result_hsame_target {x y y' d : BHist} :
    MetricDistanceWitness (BHist.e1 x) y (BHist.e1 d) -> hsame y y' ->
      (y' = BHist.Empty ∧ UnaryHistory x ∧ hsame x d) ∨
        (∃ y1 : BHist, y' = BHist.e1 y1 ∧
          MetricDistanceWitness (BHist.e1 x) y1 d) := by
  intro witness sameTarget
  have resultCases := MetricDistanceWitness_left_e1_result_cases witness
  cases resultCases with
  | inl emptyCase =>
      cases emptyCase with
      | intro yEmpty data =>
          cases yEmpty
          have targetEmpty : y' = BHist.Empty := hsame_empty_inversion sameTarget
          exact Or.inl (And.intro targetEmpty data)
  | inr visibleCase =>
      cases visibleCase with
      | intro y0 data =>
          cases data with
          | intro yEq tailWitness =>
              cases yEq
              have targetShape := hsame_e1_inversion sameTarget
              cases targetShape with
              | intro y1 tailData =>
                  cases tailData with
                  | intro targetEq sameTail =>
                      have targetCarrier : UnaryHistory y1 :=
                        unary_transport tailWitness.right.left sameTail
                      have targetCont : Cont (BHist.e1 x) y1 d :=
                        cont_hsame_transport (hsame_refl (BHist.e1 x)) sameTail
                          (hsame_refl d) tailWitness.right.right.right
                      exact
                        Or.inr
                          (Exists.intro y1
                            (And.intro targetEq
                              (And.intro tailWitness.left
                                (And.intro targetCarrier
                                  (And.intro tailWitness.right.right.left targetCont)))))

theorem MetricDistanceWitness_right_e1_result_iff {x y d : BHist} :
    MetricDistanceWitness x (BHist.e1 y) (BHist.e1 d) ↔ MetricDistanceWitness x y d := by
  constructor
  · intro witness
    exact MetricDistanceWitness_right_e1_result_exactness witness
  · intro witness
    exact And.intro witness.left
        (And.intro (unary_e1_closed witness.right.left)
          (And.intro (unary_e1_closed witness.right.right.left)
            (cont_step_one witness.right.right.right)))

theorem MetricDistanceWitness_e1_pair_result_tail_readback {x y d : BHist} :
    MetricDistanceWitness (BHist.e1 x) (BHist.e1 y) (BHist.e1 d) ->
      UnaryHistory x ∧ UnaryHistory y ∧ hsame d (append (BHist.e1 x) y) := by
  intro witness
  have tailWitness : MetricDistanceWitness (BHist.e1 x) y d :=
    Iff.mp MetricDistanceWitness_right_e1_result_iff witness
  exact And.intro (unary_e1_inversion tailWitness.left)
    (And.intro tailWitness.right.left tailWitness.right.right.right)

theorem MetricDistanceWitness_left_e1_visible_target_step {x y d : BHist} :
    MetricDistanceWitness (BHist.e1 x) y d ->
      MetricDistanceWitness (BHist.e1 x) (BHist.e1 y) (BHist.e1 d) := by
  intro witness
  exact And.intro witness.left
    (And.intro (unary_e1_closed witness.right.left)
      (And.intro (unary_e1_closed witness.right.right.left)
        (cont_step_one witness.right.right.right)))

theorem MetricDistanceWitness_left_e1_visible_target_iff {x y d : BHist} :
    MetricDistanceWitness (BHist.e1 x) (BHist.e1 y) (BHist.e1 d) ↔
      MetricDistanceWitness (BHist.e1 x) y d := by
  constructor
  · intro witness
    exact MetricDistanceWitness_left_e1_visible_target_exactness witness (hsame_refl (BHist.e1 y))
  · intro witness
    exact And.intro witness.left
      (And.intro (unary_e1_closed witness.right.left)
        (And.intro (unary_e1_closed witness.right.right.left)
          (cont_step_one witness.right.right.right)))

theorem MetricDistanceWitness_left_e1_source_step {x y d : BHist} :
    MetricDistanceWitness x y d -> MetricDistanceWitness (BHist.e1 x) y (BHist.e1 d) := by
  intro witness
  exact And.intro (unary_e1_closed witness.left)
    (And.intro witness.right.left
      (And.intro (unary_e1_closed witness.right.right.left)
        (cont_intro
          ((congrArg BHist.e1 witness.right.right.right).trans
            (unary_append_e1_left (h := y) (k := x) witness.right.left).symm))))

theorem MetricDistanceWitness_left_e1_visible_target_result_shape {x y d : BHist} :
    MetricDistanceWitness (BHist.e1 x) (BHist.e1 y) d ->
      ∃ k : BHist, hsame d (BHist.e1 k) ∧
        MetricDistanceWitness (BHist.e1 x) y k := by
  intro witness
  have resultShape := MetricDistanceWitness_left_e1_result_shape witness
  cases resultShape with
  | intro k resultData =>
      cases resultData with
      | intro sameResult branches =>
          cases branches with
          | inl emptyBranch =>
              cases emptyBranch with
              | intro targetEmpty _data =>
                  cases targetEmpty
          | inr visibleBranch =>
              cases visibleBranch with
              | intro y1 visibleData =>
                  cases visibleData with
                  | intro targetEq tailWitness =>
                      cases targetEq
                      exact Exists.intro k (And.intro sameResult tailWitness)

end BEDC.Derived.MetricUp
