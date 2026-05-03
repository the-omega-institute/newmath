import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonAddMul_context_continuation_result_carrier {L R a b c d out : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      Cont (append L (FieldSingletonAdd a b)) (append (FieldSingletonMul c d) R) out ->
        FieldSingletonCarrier out := by
  intro carrierL carrierR continuation
  unfold FieldSingletonCarrier at carrierL carrierR
  unfold FieldSingletonAdd FieldSingletonMul at continuation
  cases carrierL
  cases carrierR
  exact cont_deterministic continuation (cont_right_unit BHist.Empty)

theorem FieldSingletonAddMul_context_continuation_result_iff {L R a b c d out : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      (Cont (append L (FieldSingletonAdd a b)) (append (FieldSingletonMul c d) R) out <->
        FieldSingletonCarrier out) := by
  intro carrierL carrierR
  constructor
  · intro continuation
    exact FieldSingletonAddMul_context_continuation_result_carrier carrierL carrierR continuation
  · intro carrierOut
    unfold FieldSingletonCarrier at carrierL carrierR carrierOut
    unfold FieldSingletonAdd FieldSingletonMul
    cases carrierL
    cases carrierR
    exact cont_result_hsame_transport (cont_right_unit BHist.Empty) (hsame_symm carrierOut)

theorem FieldSingletonAddMul_context_continuation_classifier
    {L R L' R' a b c d a' b' c' d' out out' : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R -> FieldSingletonCarrier L' ->
      FieldSingletonCarrier R' ->
        Cont (append L (FieldSingletonAdd a b)) (append (FieldSingletonMul c d) R) out ->
          Cont (append L' (FieldSingletonAdd a' b'))
            (append (FieldSingletonMul c' d') R') out' ->
              FieldSingletonClassifier out out' := by
  intro carrierL carrierR carrierL' carrierR' leftContinuation rightContinuation
  have outCarrier : FieldSingletonCarrier out :=
    FieldSingletonAddMul_context_continuation_result_carrier carrierL carrierR leftContinuation
  have outCarrier' : FieldSingletonCarrier out' :=
    FieldSingletonAddMul_context_continuation_result_carrier carrierL' carrierR' rightContinuation
  exact And.intro outCarrier
    (And.intro outCarrier' (hsame_trans outCarrier (hsame_symm outCarrier')))

end BEDC.Derived.FieldUp
