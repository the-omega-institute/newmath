import BEDC.Derived.FieldUp.SingletonContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonNeg_context_continuation_classifier {L R L' R' a a' out out' : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R -> FieldSingletonCarrier L' ->
      FieldSingletonCarrier R' ->
        Cont (append L (FieldSingletonNeg a)) R out ->
          Cont (append L' (FieldSingletonNeg a')) R' out' ->
            FieldSingletonClassifier out out' := by
  intro carrierL carrierR carrierL' carrierR' leftContinuation rightContinuation
  have leftSourceCarrier : FieldSingletonCarrier (append L (FieldSingletonNeg a)) := by
    unfold FieldSingletonNeg
    exact append_eq_empty_iff.mpr (And.intro carrierL (hsame_refl BHist.Empty))
  have rightSourceCarrier : FieldSingletonCarrier (append L' (FieldSingletonNeg a')) := by
    unfold FieldSingletonNeg
    exact append_eq_empty_iff.mpr (And.intro carrierL' (hsame_refl BHist.Empty))
  have outCarrier : FieldSingletonCarrier out :=
    FieldSingletonCarrier_continuation_closed leftSourceCarrier carrierR leftContinuation
  have outCarrier' : FieldSingletonCarrier out' :=
    FieldSingletonCarrier_continuation_closed rightSourceCarrier carrierR' rightContinuation
  exact And.intro outCarrier
    (And.intro outCarrier' (hsame_trans outCarrier (hsame_symm outCarrier')))

end BEDC.Derived.FieldUp
