import BEDC.Derived.MetricUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_right_e1_result_shape {x y d : BHist} :
    MetricDistanceWitness x (BHist.e1 y) d ->
      ∃ k : BHist, hsame d (BHist.e1 k) ∧ MetricDistanceWitness x y k := by
  intro witness
  cases witness with
  | intro xCarrier rest =>
      cases rest with
      | intro yCarrier rest =>
          cases rest with
          | intro _dCarrier distance =>
              have yTailCarrier : UnaryHistory y := unary_e1_inversion yCarrier
              exact Exists.intro (append x y)
                (And.intro distance
                  (And.intro xCarrier
                    (And.intro yTailCarrier
                      (And.intro (unary_append_closed xCarrier yTailCarrier) (cont_intro rfl)))))

theorem MetricDistanceWitness_right_e1_result_not_empty {x y d : BHist} :
    MetricDistanceWitness x (BHist.e1 y) d -> hsame d BHist.Empty -> False := by
  intro witness sameEmpty
  have shape := MetricDistanceWitness_right_e1_result_shape witness
  cases shape with
  | intro k data =>
      exact not_hsame_e1_empty (hsame_trans (hsame_symm data.left) sameEmpty)

theorem MetricDistanceWitness_right_e1_result_tail_hsame_exact
    {x y d k : BHist} :
    MetricDistanceWitness x (BHist.e1 y) d -> hsame d (BHist.e1 k) ->
      MetricDistanceWitness x y k := by
  intro witness sameResult
  have shape := MetricDistanceWitness_right_e1_result_shape witness
  cases shape with
  | intro k0 data =>
      cases data with
      | intro sameD tailWitness =>
          have sameTail : hsame k0 k :=
            hsame_e1_iff.mp (hsame_trans (hsame_symm sameD) sameResult)
          cases sameTail
          exact tailWitness

theorem MetricDistanceWitness_right_e1_source_shape {x y d : BHist} :
    MetricDistanceWitness x (BHist.e1 y) d ->
      ∃ k : BHist, hsame d (BHist.e1 k) ∧
        ((x = BHist.Empty ∧ UnaryHistory y ∧ hsame k y) ∨
          ∃ x1 : BHist, x = BHist.e1 x1 ∧
            MetricDistanceWitness (BHist.e1 x1) y k) := by
  intro witness
  cases d with
  | Empty =>
      cases witness with
      | intro _xCarrier rest =>
          cases rest with
          | intro _targetCarrier rest =>
              cases rest with
              | intro _distanceCarrier distance =>
                  cases distance
  | e0 d0 =>
      exact False.elim (unary_no_zero_extension witness.right.right.left)
  | e1 k =>
      exact Exists.intro k
        (And.intro (hsame_refl (BHist.e1 k))
          (MetricDistanceWitness_right_e1_source_cases witness))

theorem MetricDistanceWitness_right_e1_result_hsame_source {x x' y d : BHist} :
    MetricDistanceWitness x (BHist.e1 y) (BHist.e1 d) -> hsame x x' ->
      (x' = BHist.Empty ∧ UnaryHistory y ∧ hsame d y) ∨
        (∃ x1 : BHist, x' = BHist.e1 x1 ∧
          MetricDistanceWitness (BHist.e1 x1) y d) := by
  intro witness sameSource
  have sourceCases := MetricDistanceWitness_right_e1_source_cases witness
  cases sourceCases with
  | inl emptyCase =>
      cases emptyCase with
      | intro xEmpty data =>
          cases xEmpty
          have sourceEmpty : x' = BHist.Empty := hsame_empty_inversion sameSource
          exact Or.inl (And.intro sourceEmpty data)
  | inr visibleCase =>
      cases visibleCase with
      | intro x0 data =>
          cases data with
          | intro xEq tailWitness =>
              cases xEq
              have sourceShape := hsame_e1_inversion sameSource
              cases sourceShape with
              | intro x1 tailData =>
                  cases tailData with
                  | intro sourceEq sameTail =>
                      have sourceCarrier : UnaryHistory x1 :=
                        unary_transport (unary_e1_inversion tailWitness.left) sameTail
                      have sourceCont : Cont (BHist.e1 x1) y d :=
                        cont_hsame_transport (hsame_e1_congr sameTail) (hsame_refl y)
                          (hsame_refl d) tailWitness.right.right.right
                      exact
                        Or.inr
                          (Exists.intro x1
                            (And.intro sourceEq
                              (And.intro (unary_e1_closed sourceCarrier)
                                (And.intro tailWitness.right.left
                                  (And.intro tailWitness.right.right.left sourceCont)))))

theorem MetricDistanceWitness_right_e1_result_e0_absurd {x y d : BHist} :
    MetricDistanceWitness x (BHist.e1 y) (BHist.e0 d) -> False := by
  intro witness
  have shape := MetricDistanceWitness_right_e1_result_shape witness
  cases shape with
  | intro k data =>
      exact not_hsame_e0_e1 data.left

theorem MetricDistanceWitness_right_e1_result_hsame_target {x y y' d : BHist} :
    MetricDistanceWitness x (BHist.e1 y) (BHist.e1 d) -> hsame y y' ->
      (x = BHist.Empty ∧ UnaryHistory y' ∧ hsame d y') ∨
        (∃ x1 : BHist, x = BHist.e1 x1 ∧
          MetricDistanceWitness (BHist.e1 x1) y' d) := by
  intro witness sameTarget
  have sourceCases := MetricDistanceWitness_right_e1_source_cases witness
  cases sourceCases with
  | inl emptyCase =>
      cases emptyCase with
      | intro xEmpty data =>
          cases data with
          | intro yCarrier sameDY =>
              have yCarrier' : UnaryHistory y' := unary_transport yCarrier sameTarget
              exact Or.inl (And.intro xEmpty (And.intro yCarrier' (hsame_trans sameDY sameTarget)))
  | inr visibleCase =>
      cases visibleCase with
      | intro x0 data =>
          cases data with
          | intro xEq tailWitness =>
              have targetCarrier : UnaryHistory y' :=
                unary_transport tailWitness.right.left sameTarget
              have targetCont : Cont (BHist.e1 x0) y' d :=
                cont_hsame_transport (hsame_refl (BHist.e1 x0)) sameTarget
                  (hsame_refl d) tailWitness.right.right.right
              exact
                Or.inr
                  (Exists.intro x0
                    (And.intro xEq
                      (And.intro tailWitness.left
                        (And.intro targetCarrier
                          (And.intro tailWitness.right.right.left targetCont)))))

theorem MetricDistanceWitness_right_e1_result_two_sided_endpoint_transport
    {x x' y y' d : BHist} :
    MetricDistanceWitness x (BHist.e1 y) (BHist.e1 d) -> hsame x x' -> hsame y y' ->
      (x' = BHist.Empty ∧ UnaryHistory y' ∧ hsame d y') ∨
        (∃ x1 : BHist, x' = BHist.e1 x1 ∧
          MetricDistanceWitness (BHist.e1 x1) y' d) := by
  intro witness sameSource sameTarget
  have sourceCases :=
    MetricDistanceWitness_right_e1_result_hsame_source witness sameSource
  cases sourceCases with
  | inl emptyCase =>
      cases emptyCase with
      | intro sourceEmpty data =>
          cases data with
          | intro targetCarrier sameResult =>
              have targetCarrier' : UnaryHistory y' := unary_transport targetCarrier sameTarget
              exact
                Or.inl
                  (And.intro sourceEmpty
                    (And.intro targetCarrier' (hsame_trans sameResult sameTarget)))
  | inr visibleCase =>
      cases visibleCase with
      | intro x1 data =>
          cases data with
          | intro sourceEq tailWitness =>
              have targetCarrier' : UnaryHistory y' :=
                unary_transport tailWitness.right.left sameTarget
              have targetCont : Cont (BHist.e1 x1) y' d :=
                cont_hsame_transport (hsame_refl (BHist.e1 x1)) sameTarget
                  (hsame_refl d) tailWitness.right.right.right
              exact
                Or.inr
                  (Exists.intro x1
                    (And.intro sourceEq
                      (And.intro tailWitness.left
                        (And.intro targetCarrier'
                          (And.intro tailWitness.right.right.left targetCont)))))

end BEDC.Derived.MetricUp
