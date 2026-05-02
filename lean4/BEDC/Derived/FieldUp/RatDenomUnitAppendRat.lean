import BEDC.Derived.FieldUp.RatDenomUnit
import BEDC.Derived.FieldUp.PositiveDenominatorAppendSplit

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

theorem RatDenomUnitCarrier_append_branch_cases {h k : BHist} :
    RatDenomUnitCarrier (append h k) ->
      (hsame h BHist.Empty ∧ hsame k BHist.Empty) ∨
        RatHistoryCarrier h ∨ RatHistoryCarrier k := by
  intro carrier
  cases carrier with
  | inl productEmpty =>
      exact Or.inl (append_eq_empty_iff.mp productEmpty)
  | inr productRat =>
      exact Or.inr (RatHistoryCarrier_append_split productRat)

end BEDC.Derived.FieldUp
