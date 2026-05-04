import BEDC.FKernel.Cont.Cancellation
import BEDC.Derived.ComplexDiffUp
import BEDC.Derived.MetricUp.Transport

namespace BEDC.Derived.DerivativeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexDiffUp
open BEDC.Derived.MetricUp

def DerivativeMetricQuotient (f z h q dist : BHist) : Prop :=
  UnaryHistory f ∧ UnaryHistory z ∧ CplxNonZero h ∧ UnaryHistory q ∧ Cont f h q ∧
    UnaryHistory h ∧ UnaryHistory dist ∧ Cont h q dist

theorem DerivativeMetricQuotient_hsame_transport
    {f f' z z' h h' q q' dist dist' : BHist} :
    hsame f f' -> hsame z z' -> hsame h h' -> hsame q q' -> hsame dist dist' ->
      DerivativeMetricQuotient f z h q dist ->
        DerivativeMetricQuotient f' z' h' q' dist' ∧
          CplxDiffQuot f' z' h' q' ∧ MetricDistanceWitness h' q' dist' ∧
            Cont f' h' q' ∧ Cont h' q' dist' := by
  intro sameF sameZ sameH sameQ sameDist quotient
  cases quotient with
  | intro functionCarrier rest =>
      cases rest with
      | intro pointCarrier rest =>
          cases rest with
          | intro stepNonzero rest =>
              cases rest with
              | intro quotientCarrier rest =>
                  cases rest with
                  | intro diffLedger rest =>
                      cases rest with
                      | intro stepCarrier rest =>
                          cases rest with
                          | intro distCarrier metricLedger =>
                              have functionCarrier' : UnaryHistory f' :=
                                unary_transport functionCarrier sameF
                              have pointCarrier' : UnaryHistory z' :=
                                unary_transport pointCarrier sameZ
                              have stepCarrier' : UnaryHistory h' :=
                                unary_transport stepCarrier sameH
                              have quotientCarrier' : UnaryHistory q' :=
                                unary_transport quotientCarrier sameQ
                              have distCarrier' : UnaryHistory dist' :=
                                unary_transport distCarrier sameDist
                              have stepNonzero' : CplxNonZero h' := by
                                intro stepEmpty
                                exact stepNonzero (hsame_trans sameH stepEmpty)
                              have diffLedger' : Cont f' h' q' :=
                                cont_hsame_transport sameF sameH sameQ diffLedger
                              have metricWitness : MetricDistanceWitness h q dist :=
                                And.intro stepCarrier
                                  (And.intro quotientCarrier
                                    (And.intro distCarrier metricLedger))
                              have metricLedger' : Cont h' q' dist' :=
                                MetricDistanceWitness_cont_hsame_transport sameH sameQ sameDist
                                  metricWitness
                              have derivative' : DerivativeMetricQuotient f' z' h' q' dist' :=
                                And.intro functionCarrier'
                                  (And.intro pointCarrier'
                                    (And.intro stepNonzero'
                                      (And.intro quotientCarrier'
                                        (And.intro diffLedger'
                                          (And.intro stepCarrier'
                                            (And.intro distCarrier' metricLedger'))))))
                              have complexQuotient' : CplxDiffQuot f' z' h' q' :=
                                And.intro functionCarrier'
                                  (And.intro pointCarrier'
                                    (And.intro stepNonzero'
                                      (And.intro quotientCarrier' diffLedger')))
                              have metricWitness' : MetricDistanceWitness h' q' dist' :=
                                And.intro stepCarrier'
                                  (And.intro quotientCarrier'
                                    (And.intro distCarrier' metricLedger'))
                              exact And.intro derivative'
                                (And.intro complexQuotient'
                                  (And.intro metricWitness'
                                    (And.intro diffLedger' metricLedger')))

theorem DerivativeMetricQuotient_distance_result_nonempty {f z h q dist : BHist} :
    DerivativeMetricQuotient f z h q dist -> hsame dist BHist.Empty -> False := by
  intro quotient sameDist
  cases quotient with
  | intro _functionCarrier rest =>
      cases rest with
      | intro _pointCarrier rest =>
          cases rest with
          | intro stepNonzero rest =>
              cases rest with
              | intro _quotientCarrier rest =>
                  cases rest with
                  | intro _diffLedger rest =>
                      cases rest with
                      | intro _stepCarrier rest =>
                          cases rest with
                          | intro _distCarrier metricLedger =>
                              have emptyLedger : Cont h q BHist.Empty :=
                                cont_result_hsame_transport metricLedger sameDist
                              have endpoints := cont_empty_result_inversion emptyLedger
                              exact stepNonzero endpoints.left

theorem DerivativeMetricQuotient_distance_cont_depth_add {f z h q dist : BHist} :
    DerivativeMetricQuotient f z h q dist ->
      Cont h q dist ∧ MetricDistanceDepth dist = MetricDistanceDepth h + MetricDistanceDepth q := by
  intro quotient
  cases quotient with
  | intro _functionCarrier rest =>
      cases rest with
      | intro _pointCarrier rest =>
          cases rest with
          | intro _stepNonzero rest =>
              cases rest with
              | intro quotientCarrier rest =>
                  cases rest with
                  | intro _diffLedger rest =>
                      cases rest with
                      | intro stepCarrier rest =>
                          cases rest with
                          | intro distCarrier metricLedger =>
                              have witness : MetricDistanceWitness h q dist :=
                                And.intro stepCarrier
                                  (And.intro quotientCarrier
                                    (And.intro distCarrier metricLedger))
                              exact And.intro metricLedger
                                (MetricDistanceWitness_depth_add witness)

theorem DerivativeCplxDiffAt_witness_step_unary {f z fp : BHist} :
    CplxDiffAt f z fp ->
      ∃ h : BHist, ∃ q : BHist, UnaryHistory h ∧ UnaryHistory q ∧ Cont f h q ∧ hsame q fp := by
  intro derivative
  cases derivative with
  | intro _functionCarrier derivativeRest =>
      cases derivativeRest with
      | intro _pointCarrier derivativeRest =>
          cases derivativeRest with
          | intro _derivativeCarrier derivativeRest =>
              cases derivativeRest with
              | intro witness classifier =>
                  cases witness with
                  | intro h witnessRest =>
                      cases witnessRest with
                      | intro q quotient =>
                          have stepUnary := CplxDiffQuot_step_unary quotient
                          exact Exists.intro h
                            (Exists.intro q
                              (And.intro stepUnary.left
                                (And.intro stepUnary.right.left
                                  (And.intro stepUnary.right.right (classifier quotient)))))

theorem DerivativeCplxDiffAt_derivative_nonempty {f z fp : BHist} :
    CplxDiffAt f z fp -> hsame fp BHist.Empty -> False := by
  intro derivative derivativeEmpty
  cases derivative with
  | intro _functionCarrier derivativeRest =>
      cases derivativeRest with
      | intro _pointCarrier derivativeRest =>
          cases derivativeRest with
          | intro _derivativeCarrier derivativeRest =>
              cases derivativeRest with
              | intro witness classifier =>
                  cases witness with
                  | intro h witnessRest =>
                      cases witnessRest with
                      | intro q quotient =>
                          have quotientEmpty : hsame q BHist.Empty :=
                            hsame_trans (classifier quotient) derivativeEmpty
                          exact CplxDiffQuot_result_nonempty quotient quotientEmpty

theorem DerivativeMetricQuotient_quotient_distance_nonempty {f z h q dist : BHist} :
    DerivativeMetricQuotient f z h q dist ->
      (hsame q BHist.Empty -> False) ∧ (hsame dist BHist.Empty -> False) := by
  intro quotient
  cases quotient with
  | intro functionCarrier rest =>
      cases rest with
      | intro pointCarrier rest =>
          cases rest with
          | intro stepNonzero rest =>
              cases rest with
              | intro quotientCarrier rest =>
                  cases rest with
                  | intro diffLedger rest =>
                      cases rest with
                      | intro stepCarrier rest =>
                          cases rest with
                          | intro distCarrier metricLedger =>
                              have complexQuotient : CplxDiffQuot f z h q :=
                                And.intro functionCarrier
                                  (And.intro pointCarrier
                                    (And.intro stepNonzero
                                      (And.intro quotientCarrier diffLedger)))
                              constructor
                              · exact CplxDiffQuot_result_nonempty complexQuotient
                              · intro distEmpty
                                have emptyMetricLedger : Cont h q BHist.Empty :=
                                  cont_result_hsame_transport metricLedger distEmpty
                                have endpoints := cont_empty_result_inversion emptyMetricLedger
                                exact stepNonzero endpoints.left

theorem DerivativeMetricQuotient_result_deterministic {f z h q q' dist dist' : BHist} :
    DerivativeMetricQuotient f z h q dist ->
      DerivativeMetricQuotient f z h q' dist' ->
        Cont f h q ∧ Cont f h q' ∧ Cont h q dist ∧ Cont h q' dist' ∧
          hsame q q' ∧ hsame dist dist' := by
  intro left right
  cases left with
  | intro _functionCarrier leftRest =>
      cases leftRest with
      | intro _pointCarrier leftRest =>
          cases leftRest with
          | intro _stepNonzero leftRest =>
              cases leftRest with
              | intro _quotientCarrier leftRest =>
                  cases leftRest with
                  | intro leftFunctionLedger leftRest =>
                      cases leftRest with
                      | intro _stepCarrier leftRest =>
                          cases leftRest with
                          | intro _distCarrier leftMetricLedger =>
                              cases right with
                              | intro _functionCarrier' rightRest =>
                                  cases rightRest with
                                  | intro _pointCarrier' rightRest =>
                                      cases rightRest with
                                      | intro _stepNonzero' rightRest =>
                                          cases rightRest with
                                          | intro _quotientCarrier' rightRest =>
                                              cases rightRest with
                                              | intro rightFunctionLedger rightRest =>
                                                  cases rightRest with
                                                  | intro _stepCarrier' rightRest =>
                                                      cases rightRest with
                                                      | intro _distCarrier' rightMetricLedger =>
                                                          have sameQuotient : hsame q q' :=
                                                            cont_deterministic leftFunctionLedger
                                                              rightFunctionLedger
                                                          have rightMetricAtLeftQuotient :
                                                              Cont h q dist' :=
                                                            cont_hsame_transport (hsame_refl h)
                                                              (hsame_symm sameQuotient)
                                                              (hsame_refl dist') rightMetricLedger
                                                          have sameDistance : hsame dist dist' :=
                                                            cont_deterministic leftMetricLedger
                                                              rightMetricAtLeftQuotient
                                                          exact And.intro leftFunctionLedger
                                                            (And.intro rightFunctionLedger
                                                              (And.intro leftMetricLedger
                                                              (And.intro rightMetricLedger
                                                                (And.intro sameQuotient
                                                                  sameDistance))))

theorem DerivativeMetricQuotient_same_quotient_step_distance_deterministic
    {f z h h' q dist dist' : BHist} :
    DerivativeMetricQuotient f z h q dist ->
      DerivativeMetricQuotient f z h' q dist' ->
        hsame h h' ∧ hsame dist dist' ∧ Cont f h q ∧ Cont f h' q ∧
          Cont h q dist ∧ Cont h' q dist' := by
  intro left right
  have leftQuotient : CplxDiffQuot f z h q :=
    And.intro left.left
      (And.intro left.right.left
        (And.intro left.right.right.left
          (And.intro left.right.right.right.left left.right.right.right.right.left)))
  have rightQuotient : CplxDiffQuot f z h' q :=
    And.intro right.left
      (And.intro right.right.left
        (And.intro right.right.right.left
          (And.intro right.right.right.right.left right.right.right.right.right.left)))
  have sameStepData :=
    CplxDiffQuot_same_result_step_deterministic leftQuotient rightQuotient
  have leftMetricLedger : Cont h q dist :=
    left.right.right.right.right.right.right.right
  have rightMetricLedger : Cont h' q dist' :=
    right.right.right.right.right.right.right.right
  have rightMetricAtLeftStep : Cont h q dist' :=
    cont_hsame_transport (hsame_symm sameStepData.left) (hsame_refl q)
      (hsame_refl dist') rightMetricLedger
  have sameDistance : hsame dist dist' :=
    cont_deterministic leftMetricLedger rightMetricAtLeftStep
  exact And.intro sameStepData.left
    (And.intro sameDistance
      (And.intro sameStepData.right.left
        (And.intro sameStepData.right.right
          (And.intro leftMetricLedger rightMetricLedger))))

theorem DerivativeMetricQuotient_visible_step_same_quotient_absurd
    {f z p q out dist0 dist1 : BHist} :
    DerivativeMetricQuotient f z (BHist.e0 p) out dist0 ->
      DerivativeMetricQuotient f z (BHist.e1 q) out dist1 -> False := by
  intro left right
  have sameStep : hsame (BHist.e0 p) (BHist.e1 q) :=
    (DerivativeMetricQuotient_same_quotient_step_distance_deterministic left right).left
  exact not_hsame_e0_e1 sameStep

theorem DerivativeMetricQuotient_distance_visible_context_readback {p r f z h q dist core : BHist} :
    DerivativeMetricQuotient f z h q dist ->
      hsame (append (append p dist) r) (append (append p core) r) ->
        hsame dist core ∧ (hsame core BHist.Empty -> False) := by
  intro quotient sameVisible
  have sameNested : hsame (append p (append dist r)) (append p (append core r)) :=
    hsame_trans (hsame_symm (append_assoc p dist r))
      (hsame_trans sameVisible (append_assoc p core r))
  have sameCore : hsame dist core :=
    (append_hsame_common_context_cancel_iff (hsame_refl p) (hsame_refl r)).mp sameNested
  exact And.intro sameCore
    (fun coreEmpty =>
      DerivativeMetricQuotient_distance_result_nonempty quotient
        (hsame_trans sameCore coreEmpty))

theorem DerivativeMetricQuotient_quotient_visible_context_readback
    {p r f z h q dist core : BHist} :
    DerivativeMetricQuotient f z h q dist ->
      hsame (append (append p q) r) (append (append p core) r) ->
        hsame q core ∧ (hsame core BHist.Empty -> False) := by
  intro quotient sameVisible
  have sameNested : hsame (append p (append q r)) (append p (append core r)) :=
    hsame_trans (hsame_symm (append_assoc p q r))
      (hsame_trans sameVisible (append_assoc p core r))
  have sameCore : hsame q core :=
    (append_hsame_common_context_cancel_iff (hsame_refl p) (hsame_refl r)).mp sameNested
  exact And.intro sameCore
    (fun coreEmpty =>
      (DerivativeMetricQuotient_quotient_distance_nonempty quotient).left
        (hsame_trans sameCore coreEmpty))

end BEDC.Derived.DerivativeUp
