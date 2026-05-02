import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatDenomUnitCarrier_append_left_rat_closed {h k : BHist} :
    RatHistoryCarrier h -> RatDenomUnitCarrier k -> RatHistoryCarrier (append h k) := by
  intro carrierH carrierK
  cases carrierK with
  | inl emptyK =>
      cases emptyK
      exact carrierH
  | inr ratK =>
      exact field_rat_denominator_continuation_carrier_closure carrierH ratK (cont_intro rfl)

theorem RatDenomUnitCarrier_append_right_rat_closed {h k : BHist} :
    RatDenomUnitCarrier h -> RatHistoryCarrier k -> RatHistoryCarrier (append h k) := by
  intro carrierH carrierK
  cases carrierH with
  | inl emptyH =>
      cases emptyH
      exact RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left k)) carrierK
  | inr ratH =>
      exact field_rat_denominator_continuation_carrier_closure ratH carrierK (cont_intro rfl)

end BEDC.Derived.FieldUp
