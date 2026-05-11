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

theorem DerivativeMetricQuotient_function_prefix_closed {p f z h q dist : BHist} :
    UnaryHistory p -> DerivativeMetricQuotient f z h q dist ->
      DerivativeMetricQuotient (append p f) z h (append p q) (append h (append p q)) := by
  intro prefixCarrier quotient
  cases quotient with
  | intro functionCarrier rest =>
      cases rest with
      | intro pointCarrier rest =>
          cases rest with
          | intro stepNonzero rest =>
              cases rest with
              | intro quotientCarrier rest =>
                  cases rest with
                  | intro functionLedger rest =>
                      cases rest with
                      | intro stepCarrier rest =>
                          cases rest with
                          | intro _distanceCarrier _metricLedger =>
                              have prefixedFunctionCarrier : UnaryHistory (append p f) :=
                                unary_append_closed prefixCarrier functionCarrier
                              have prefixedQuotientCarrier : UnaryHistory (append p q) :=
                                unary_append_closed prefixCarrier quotientCarrier
                              have prefixedFunctionLedger :
                                  Cont (append p f) h (append p q) := by
                                apply cont_intro
                                exact
                                  (congrArg (append p) functionLedger).trans
                                    (append_assoc p f h).symm
                              have prefixedDistanceCarrier :
                                  UnaryHistory (append h (append p q)) :=
                                unary_append_closed stepCarrier prefixedQuotientCarrier
                              exact
                                And.intro prefixedFunctionCarrier
                                  (And.intro pointCarrier
                                    (And.intro stepNonzero
                                      (And.intro prefixedQuotientCarrier
                                        (And.intro prefixedFunctionLedger
                                          (And.intro stepCarrier
                                            (And.intro prefixedDistanceCarrier
                                              (cont_intro rfl)))))))

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

theorem DerivativeMetricQuotient_empty_function_step_readback {z h q dist : BHist} :
    DerivativeMetricQuotient BHist.Empty z h q dist ->
      hsame q h ∧ Cont h q dist ∧ hsame dist (append h h) := by
  intro quotient
  have functionLedger : Cont BHist.Empty h q := quotient.right.right.right.right.left
  have sameQH : hsame q h := cont_left_unit_result functionLedger
  have metricLedger : Cont h q dist := quotient.right.right.right.right.right.right.right
  have sameDistHQ : hsame dist (append h q) := metricLedger
  have sameHQHH : hsame (append h q) (append h h) := congrArg (append h) sameQH
  exact And.intro sameQH (And.intro metricLedger (hsame_trans sameDistHQ sameHQHH))

theorem DerivativeMetricQuotient_empty_function_zero_step_absurd {z h q dist s : BHist} :
    DerivativeMetricQuotient BHist.Empty z h q dist -> hsame h (BHist.e0 s) -> False := by
  intro quotient sameStep
  have visibleStep : UnaryHistory (BHist.e0 s) :=
    unary_transport quotient.right.right.right.right.right.left sameStep
  exact unary_no_zero_extension visibleStep

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

theorem DerivativeCplxDiffAt_empty_function_step_readback {z fp : BHist} :
    CplxDiffAt BHist.Empty z fp ->
      ∃ h : BHist, CplxNonZero h ∧ UnaryHistory h ∧ hsame fp h := by
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
                          have stepData := CplxDiffQuot_step_unary quotient
                          have ledger : Cont BHist.Empty h q := stepData.right.right
                          have sameQH : hsame q h := cont_left_unit_result ledger
                          have sameFpH : hsame fp h :=
                            hsame_trans (hsame_symm (classifier quotient)) sameQH
                          exact Exists.intro h
                            (And.intro quotient.right.right.left
                              (And.intro stepData.left sameFpH))

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

theorem DerivativeMetricQuotient_hsame_step_result_deterministic
    {f z h h' q q' dist dist' : BHist} :
    hsame h h' -> DerivativeMetricQuotient f z h q dist ->
      DerivativeMetricQuotient f z h' q' dist' ->
        hsame q q' ∧ hsame dist dist' ∧ Cont f h q ∧ Cont f h' q' ∧
          Cont h q dist ∧ Cont h' q' dist' := by
  intro sameStep left right
  have leftFunctionLedger : Cont f h q :=
    left.right.right.right.right.left
  have rightFunctionLedger : Cont f h' q' :=
    right.right.right.right.right.left
  have rightFunctionAtLeftStep : Cont f h q' :=
    cont_hsame_transport (hsame_refl f) (hsame_symm sameStep) (hsame_refl q')
      rightFunctionLedger
  have sameQuotient : hsame q q' :=
    cont_deterministic leftFunctionLedger rightFunctionAtLeftStep
  have leftMetricLedger : Cont h q dist :=
    left.right.right.right.right.right.right.right
  have rightMetricLedger : Cont h' q' dist' :=
    right.right.right.right.right.right.right.right
  have rightMetricAtLeftInputs : Cont h q dist' :=
    cont_hsame_transport (hsame_symm sameStep) (hsame_symm sameQuotient)
      (hsame_refl dist') rightMetricLedger
  have sameDistance : hsame dist dist' :=
    cont_deterministic leftMetricLedger rightMetricAtLeftInputs
  exact And.intro sameQuotient
    (And.intro sameDistance
      (And.intro leftFunctionLedger
        (And.intro rightFunctionLedger
          (And.intro leftMetricLedger rightMetricLedger))))

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

theorem DerivativeMetricQuotient_visible_step_hsame_quotient_absurd
    {f z p q out out' dist0 dist1 : BHist} :
    hsame out out' ->
      DerivativeMetricQuotient f z (BHist.e0 p) out dist0 ->
        DerivativeMetricQuotient f z (BHist.e1 q) out' dist1 -> False := by
  intro sameQuotient left right
  have rightAtLeftQuotient : DerivativeMetricQuotient f z (BHist.e1 q) out dist1 :=
    (DerivativeMetricQuotient_hsame_transport
      (hsame_refl f) (hsame_refl z) (hsame_refl (BHist.e1 q))
      (hsame_symm sameQuotient) (hsame_refl dist1) right).left
  exact DerivativeMetricQuotient_visible_step_same_quotient_absurd left rightAtLeftQuotient

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

theorem DerivativeMetricQuotient_step_visible_context_readback
    {p r f z h q dist core : BHist} :
    DerivativeMetricQuotient f z h q dist ->
      hsame (append (append p h) r) (append (append p core) r) ->
        hsame h core ∧ UnaryHistory core ∧ (hsame core BHist.Empty -> False) := by
  intro quotient sameVisible
  have sameNested : hsame (append p (append h r)) (append p (append core r)) :=
    hsame_trans (hsame_symm (append_assoc p h r))
      (hsame_trans sameVisible (append_assoc p core r))
  have sameCore : hsame h core :=
    (append_hsame_common_context_cancel_iff (hsame_refl p) (hsame_refl r)).mp sameNested
  have coreCarrier : UnaryHistory core :=
    unary_transport quotient.right.right.right.right.right.left sameCore
  exact And.intro sameCore
    (And.intro coreCarrier
      (fun coreEmpty => quotient.right.right.left (hsame_trans sameCore coreEmpty)))

theorem DerivativeMetricQuotient_point_visible_context_readback
    {p r f z h q dist core : BHist} :
    DerivativeMetricQuotient f z h q dist ->
      hsame (append (append p z) r) (append (append p core) r) ->
        hsame z core ∧ UnaryHistory core := by
  intro quotient sameVisible
  have sameNested : hsame (append p (append z r)) (append p (append core r)) :=
    hsame_trans (hsame_symm (append_assoc p z r))
      (hsame_trans sameVisible (append_assoc p core r))
  have sameCore : hsame z core :=
    (append_hsame_common_context_cancel_iff (hsame_refl p) (hsame_refl r)).mp sameNested
  exact And.intro sameCore (unary_transport quotient.right.left sameCore)

theorem DerivativeMetricQuotient_function_visible_context_readback
    {p r f z h q dist core : BHist} :
    DerivativeMetricQuotient f z h q dist ->
      hsame (append (append p f) r) (append (append p core) r) ->
        hsame f core ∧ UnaryHistory core := by
  intro quotient sameVisible
  have sameNested : hsame (append p (append f r)) (append p (append core r)) :=
    hsame_trans (hsame_symm (append_assoc p f r))
      (hsame_trans sameVisible (append_assoc p core r))
  have sameCore : hsame f core :=
    (append_hsame_common_context_cancel_iff (hsame_refl p) (hsame_refl r)).mp sameNested
  exact And.intro sameCore (unary_transport quotient.left sameCore)

theorem DerivativeMetricQuotient_chain_product_composition
    {f g z h_f h_g h_fg q_f q_g q_fg d_f d_g d_fg F_fg : BHist} :
    DerivativeMetricQuotient f z h_f q_f d_f ->
      DerivativeMetricQuotient g q_f h_g q_g d_g ->
        Cont h_f h_g h_fg -> Cont q_f q_g q_fg -> Cont d_f d_g d_fg ->
          Cont f g F_fg -> Cont f h_fg q_g ->
            DerivativeMetricQuotient F_fg z h_fg q_fg d_fg ∧
              Cont d_f d_g d_fg ∧ Cont q_f h_g q_g ∧ hsame g q_f := by
  intro left right stepProduct quotientProduct distanceProduct functionProduct chainLedger
  have leftFunctionLedger : Cont f h_f q_f :=
    left.right.right.right.right.left
  have rightFunctionLedger : Cont g h_g q_g :=
    right.right.right.right.right.left
  have innerQuotientLedger : Cont q_f h_g q_g :=
    cont_composite_right_factor leftFunctionLedger stepProduct chainLedger
  have sameFunctionQuotient : hsame g q_f :=
    hsame_symm (cont_right_cancel innerQuotientLedger rightFunctionLedger)
  have functionCarrier : UnaryHistory F_fg :=
    unary_cont_closed left.left right.left functionProduct
  have stepCarrier : UnaryHistory h_fg :=
    unary_cont_closed left.right.right.right.right.right.left
      right.right.right.right.right.right.left stepProduct
  have quotientCarrier : UnaryHistory q_fg :=
    unary_cont_closed left.right.right.right.left right.right.right.right.left
      quotientProduct
  have distanceCarrier : UnaryHistory d_fg :=
    unary_cont_closed left.right.right.right.right.right.right.left
      right.right.right.right.right.right.right.left distanceProduct
  have stepNonzero : CplxNonZero h_fg := by
    intro stepEmpty
    have endpoints :=
      cont_empty_result_inversion (cont_result_hsame_transport stepProduct stepEmpty)
    exact left.right.right.left endpoints.left
  have quotientLedger : Cont F_fg h_fg q_fg := by
    have sameResult : hsame (append F_fg h_fg) q_fg := by
      cases functionProduct
      cases stepProduct
      cases quotientProduct
      cases leftFunctionLedger
      cases rightFunctionLedger
      exact
        (append_assoc f g (append h_f h_g)).trans
          ((congrArg (append f)
            ((append_assoc g h_f h_g).symm.trans
              ((congrArg (fun tail => append tail h_g)
                (unary_append_comm right.left left.right.right.right.right.right.left)).trans
                  (append_assoc h_f g h_g)))).trans
            (append_assoc f h_f (append g h_g)).symm)
    exact cont_result_hsame_transport (cont_intro rfl) sameResult
  have metricLedger : Cont h_fg q_fg d_fg := by
    have sameResult : hsame (append h_fg q_fg) d_fg := by
      cases stepProduct
      cases quotientProduct
      cases distanceProduct
      cases left.right.right.right.right.right.right.right
      cases right.right.right.right.right.right.right.right
      exact
        (append_assoc h_f h_g (append q_f q_g)).trans
          ((congrArg (append h_f)
            ((append_assoc h_g q_f q_g).symm.trans
              ((congrArg (fun tail => append tail q_g)
                (unary_append_comm right.right.right.right.right.right.left
                  left.right.right.right.left)).trans
                  (append_assoc q_f h_g q_g)))).trans
            (append_assoc h_f q_f (append h_g q_g)).symm)
    exact cont_result_hsame_transport (cont_intro rfl) sameResult
  have quotient :
      DerivativeMetricQuotient F_fg z h_fg q_fg d_fg :=
    And.intro functionCarrier
      (And.intro left.right.left
        (And.intro stepNonzero
          (And.intro quotientCarrier
            (And.intro quotientLedger
              (And.intro stepCarrier
                (And.intro distanceCarrier metricLedger))))))
  exact And.intro quotient
    (And.intro distanceProduct
      (And.intro innerQuotientLedger sameFunctionQuotient))

theorem DerivativeUp_StdBridge
    {f g z h_f h_g h_fg q_f q_g q_fg d_f d_g d_fg F_fg : BHist} :
    DerivativeMetricQuotient f z h_f q_f d_f ->
      DerivativeMetricQuotient g q_f h_g q_g d_g ->
        Cont h_f h_g h_fg -> Cont q_f q_g q_fg -> Cont d_f d_g d_fg ->
          Cont f g F_fg -> Cont f h_fg q_g ->
            DerivativeMetricQuotient F_fg z h_fg q_fg d_fg ∧
              Cont d_f d_g d_fg ∧ Cont q_f h_g q_g ∧ hsame g q_f := by
  exact DerivativeMetricQuotient_chain_product_composition

end BEDC.Derived.DerivativeUp
