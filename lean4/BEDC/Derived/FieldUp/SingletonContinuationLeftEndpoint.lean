import BEDC.Derived.FieldUp.SingletonContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonCarrier_continuation_left_endpoint_iff {P Q R : BHist} :
    FieldSingletonCarrier Q -> Cont P Q R ->
      (FieldSingletonCarrier R <-> FieldSingletonCarrier P) := by
  intro carrierQ continuation
  constructor
  · intro carrierR
    cases carrierQ
    have sameRP : hsame R P := cont_deterministic continuation (cont_right_unit P)
    exact hsame_trans (hsame_symm sameRP) carrierR
  · intro carrierP
    exact FieldSingletonCarrier_continuation_closed carrierP carrierQ continuation

end BEDC.Derived.FieldUp
