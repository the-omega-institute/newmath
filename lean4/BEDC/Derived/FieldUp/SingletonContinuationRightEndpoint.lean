import BEDC.Derived.FieldUp.SingletonContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonCarrier_continuation_right_endpoint_iff {P Q R : BHist} :
    FieldSingletonCarrier P -> Cont P Q R ->
      (FieldSingletonCarrier R ↔ FieldSingletonCarrier Q) := by
  intro carrierP continuation
  constructor
  · intro carrierR
    cases carrierP
    have sameRQ : hsame R Q := cont_left_unit_result continuation
    exact hsame_trans (hsame_symm sameRQ) carrierR
  · intro carrierQ
    exact FieldSingletonCarrier_continuation_closed carrierP carrierQ continuation

end BEDC.Derived.FieldUp
