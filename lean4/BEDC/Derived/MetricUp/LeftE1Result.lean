import BEDC.Derived.MetricUp

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

end BEDC.Derived.MetricUp
