import BEDC.Derived.MetricUp
import BEDC.FKernel.Cont.Cancellation
import BEDC.Derived.MetricUp.Transport

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

theorem MetricDistanceWitness_left_e1_result_empty_target_iff {x y d : BHist} :
    MetricDistanceWitness (BHist.e1 x) y (BHist.e1 d) ->
      (hsame y BHist.Empty ↔ UnaryHistory x ∧ hsame x d) := by
  intro witness
  constructor
  · intro sameTargetEmpty
    cases y with
    | Empty =>
        have data := MetricDistanceWitness_left_e1_empty_target_exactness witness
        exact And.intro data.left (hsame_symm data.right)
    | e0 y0 =>
        exact False.elim (not_hsame_e0_empty sameTargetEmpty)
    | e1 y1 =>
        exact False.elim (not_hsame_e1_empty sameTargetEmpty)
  · intro data
    cases y with
    | Empty =>
        exact hsame_refl BHist.Empty
    | e0 y0 =>
        exact False.elim (unary_no_zero_extension witness.right.left)
    | e1 y1 =>
        have sameResult : hsame (BHist.e1 d) (BHist.e1 x) :=
          hsame_e1_congr (hsame_symm data.right)
        have cycle : Cont (BHist.e1 x) (BHist.e1 y1) (BHist.e1 x) :=
          cont_result_hsame_transport witness.right.right.right sameResult
        exact False.elim (not_hsame_e1_empty (cont_right_unit_unique cycle))

theorem MetricDistanceWitness_left_e1_result_hsame_source {x x' y d : BHist} :
    MetricDistanceWitness (BHist.e1 x) y (BHist.e1 d) -> hsame x x' ->
      (y = BHist.Empty ∧ UnaryHistory x' ∧ hsame x' d) ∨
        (∃ y1 : BHist, y = BHist.e1 y1 ∧ MetricDistanceWitness (BHist.e1 x') y1 d) := by
  intro witness sameSource
  cases sameSource
  exact MetricDistanceWitness_left_e1_result_cases witness

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

theorem MetricDistanceWitness_left_e1_result_hsame_result {x y d d' : BHist} :
    MetricDistanceWitness (BHist.e1 x) y (BHist.e1 d) -> hsame d d' ->
      (y = BHist.Empty ∧ UnaryHistory x ∧ hsame x d') ∨
        (∃ y1 : BHist, y = BHist.e1 y1 ∧
          MetricDistanceWitness (BHist.e1 x) y1 d') := by
  intro witness sameTail
  have sameResult : hsame (BHist.e1 d) (BHist.e1 d') := hsame_e1_congr sameTail
  have transported :
      MetricDistanceWitness (BHist.e1 x) y (BHist.e1 d') :=
    MetricDistanceWitness_hsame_fields_transport (hsame_refl (BHist.e1 x)) (hsame_refl y)
      sameResult witness
  exact MetricDistanceWitness_left_e1_result_cases transported

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

theorem MetricDistanceWitness_e1_pair_result_iff {x y d : BHist} :
    MetricDistanceWitness (BHist.e1 x) (BHist.e1 y) (BHist.e1 d) ↔
      UnaryHistory x ∧ UnaryHistory y ∧ hsame d (append (BHist.e1 x) y) := by
  constructor
  · intro witness
    exact MetricDistanceWitness_e1_pair_result_tail_readback witness
  · intro tailData
    have sourceCarrier : UnaryHistory (BHist.e1 x) :=
      unary_e1_closed tailData.left
    have distanceCarrier : UnaryHistory d :=
      unary_transport
        (unary_append_closed sourceCarrier tailData.right.left)
        (hsame_symm tailData.right.right)
    have central : MetricDistanceWitness (BHist.e1 x) y d :=
      And.intro sourceCarrier
        (And.intro tailData.right.left
          (And.intro distanceCarrier tailData.right.right))
    exact And.intro central.left
      (And.intro (unary_e1_closed central.right.left)
        (And.intro (unary_e1_closed central.right.right.left)
          (cont_step_one central.right.right.right)))

theorem MetricDistanceWitness_e1_pair_result_tail_exactness_iff {x y d : BHist} :
    MetricDistanceWitness (BHist.e1 x) (BHist.e1 y) (BHist.e1 d) ↔
      UnaryHistory x ∧ UnaryHistory y ∧ hsame d (append (BHist.e1 x) y) := by
  constructor
  · intro witness
    exact MetricDistanceWitness_e1_pair_result_tail_readback witness
  · intro data
    cases data with
    | intro xCarrier rest =>
        cases rest with
        | intro yCarrier sameDistance =>
            have central :
                MetricDistanceWitness (BHist.e1 x) y d :=
              And.intro (unary_e1_closed xCarrier)
                (And.intro yCarrier
                  (And.intro
                    (unary_transport
                      (unary_append_closed (unary_e1_closed xCarrier) yCarrier)
                      (hsame_symm sameDistance))
                    (cont_intro sameDistance)))
            exact And.intro central.left
              (And.intro (unary_e1_closed central.right.left)
                (And.intro (unary_e1_closed central.right.right.left)
                  (cont_step_one central.right.right.right)))

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

theorem MetricDistanceWitness_left_e1_source_iff {x y d : BHist} :
    MetricDistanceWitness (BHist.e1 x) y (BHist.e1 d) ↔
      MetricDistanceWitness x y d := by
  constructor
  · intro witness
    cases y with
    | Empty =>
        exact (MetricDistanceWitness_empty_right_iff (x := x) (d := d)).mpr
          (MetricDistanceWitness_left_e1_empty_target_exactness witness)
    | e0 y0 =>
        exact False.elim (unary_no_zero_extension witness.right.left)
    | e1 y1 =>
        have xCarrier : UnaryHistory x := unary_e1_inversion witness.left
        have yCarrier : UnaryHistory y1 := unary_e1_inversion witness.right.left
        have dCarrier : UnaryHistory d := unary_e1_inversion witness.right.right.left
        have tailResult : hsame d (append (BHist.e1 x) y1) :=
          hsame_e1_iff.mp witness.right.right.right
        exact And.intro xCarrier
          (And.intro witness.right.left
            (And.intro dCarrier
              (cont_intro
                (tailResult.trans (unary_append_e1_left (h := y1) (k := x) yCarrier)))))
  · intro witness
    exact MetricDistanceWitness_left_e1_source_step witness

theorem MetricDistanceWitness_left_e1_source_result_iff {x y d : BHist} :
    MetricDistanceWitness (BHist.e1 x) y (BHist.e1 d) ↔ MetricDistanceWitness x y d := by
  constructor
  · intro witness
    have tailEq :
        d = append x y :=
      BHist.e1.inj
        (witness.right.right.right.trans
          (unary_append_e1_left (h := y) (k := x) witness.right.left))
    exact And.intro (unary_e1_inversion witness.left)
      (And.intro witness.right.left
        (And.intro (unary_e1_inversion witness.right.right.left) tailEq))
  · intro witness
    exact MetricDistanceWitness_left_e1_source_step witness

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

theorem MetricDistanceWitness_left_e1_visible_target_result_tail_hsame_exact
    {x y d k : BHist} :
    MetricDistanceWitness (BHist.e1 x) (BHist.e1 y) d ->
      hsame d (BHist.e1 k) -> MetricDistanceWitness (BHist.e1 x) y k := by
  intro witness sameResult
  have shape := MetricDistanceWitness_left_e1_visible_target_result_shape witness
  cases shape with
  | intro k0 data =>
      cases data with
      | intro sameD tailWitness =>
          have sameTail : hsame k0 k :=
            hsame_e1_iff.mp (hsame_trans (hsame_symm sameD) sameResult)
          cases sameTail
          exact tailWitness

end BEDC.Derived.MetricUp
