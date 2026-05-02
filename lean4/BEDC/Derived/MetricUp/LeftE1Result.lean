import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

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

end BEDC.Derived.MetricUp
