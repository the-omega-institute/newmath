import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonMulInv_context_continuation_classifier
    {L R L' R' a b c d out out' : BHist} (p : FieldSingletonNonZero c)
    (q : FieldSingletonNonZero d) :
    FieldSingletonCarrier L -> FieldSingletonCarrier R -> FieldSingletonCarrier L' ->
      FieldSingletonCarrier R' ->
        Cont (append L (FieldSingletonMul a b)) (append (FieldSingletonInv c p) R) out ->
          Cont (append L' (FieldSingletonMul a b)) (append (FieldSingletonInv d q) R')
            out' ->
              FieldSingletonClassifier out out' := by
  intro carrierL carrierR carrierL' carrierR' leftContinuation rightContinuation
  have outCarrier : FieldSingletonCarrier out := by
    unfold FieldSingletonCarrier
    unfold FieldSingletonMul FieldSingletonInv at leftContinuation
    unfold FieldSingletonCarrier at carrierL carrierR
    cases carrierL
    cases carrierR
    exact cont_deterministic leftContinuation (cont_right_unit BHist.Empty)
  have outCarrier' : FieldSingletonCarrier out' := by
    unfold FieldSingletonCarrier
    unfold FieldSingletonMul FieldSingletonInv at rightContinuation
    unfold FieldSingletonCarrier at carrierL' carrierR'
    cases carrierL'
    cases carrierR'
    exact cont_deterministic rightContinuation (cont_right_unit BHist.Empty)
  exact And.intro outCarrier
    (And.intro outCarrier' (hsame_trans outCarrier (hsame_symm outCarrier')))

end BEDC.Derived.FieldUp
