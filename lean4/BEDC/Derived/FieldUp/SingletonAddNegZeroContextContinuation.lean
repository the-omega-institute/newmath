import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonAddNegZero_context_continuation_result_carrier {L R a b c out : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      Cont (append L (FieldSingletonAdd a b)) (append (FieldSingletonNeg c) R) out ->
        FieldSingletonCarrier out := by
  intro carrierL carrierR continuation
  unfold FieldSingletonCarrier
  unfold FieldSingletonAdd FieldSingletonNeg at continuation
  unfold FieldSingletonCarrier at carrierL carrierR
  cases carrierL
  cases carrierR
  exact cont_deterministic continuation (cont_right_unit BHist.Empty)

theorem FieldSingletonAddNegZero_context_continuation_result_iff {L R a b c out : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      (Cont (append L (FieldSingletonAdd a b)) (append (FieldSingletonNeg c) R) out <->
        FieldSingletonCarrier out) := by
  intro carrierL carrierR
  constructor
  · intro continuation
    exact FieldSingletonAddNegZero_context_continuation_result_carrier carrierL carrierR
      continuation
  · intro carrierOut
    unfold FieldSingletonCarrier at carrierL carrierR carrierOut
    unfold FieldSingletonAdd FieldSingletonNeg
    cases carrierL
    cases carrierR
    exact cont_result_hsame_transport (cont_right_unit BHist.Empty) (hsame_symm carrierOut)

theorem FieldSingletonAddNegZero_context_continuation_classifier {L R a b c d out out' : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      Cont (append L (FieldSingletonAdd a b)) (append (FieldSingletonNeg c) R) out ->
      Cont (append L FieldSingletonZero) (append (FieldSingletonAdd c d) R) out' ->
        FieldSingletonClassifier out out' := by
  intro carrierL carrierR leftContinuation rightContinuation
  have outCarrier : FieldSingletonCarrier out := by
    unfold FieldSingletonCarrier
    unfold FieldSingletonAdd FieldSingletonNeg at leftContinuation
    unfold FieldSingletonCarrier at carrierL carrierR
    cases carrierL
    cases carrierR
    exact cont_deterministic leftContinuation (cont_right_unit BHist.Empty)
  have outCarrier' : FieldSingletonCarrier out' := by
    unfold FieldSingletonCarrier
    unfold FieldSingletonZero FieldSingletonAdd at rightContinuation
    unfold FieldSingletonCarrier at carrierL carrierR
    cases carrierL
    cases carrierR
    exact cont_deterministic rightContinuation (cont_right_unit BHist.Empty)
  exact And.intro outCarrier
    (And.intro outCarrier' (hsame_trans outCarrier (hsame_symm outCarrier')))

end BEDC.Derived.FieldUp
