import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatDenomUnitCarrier_continuation_result_empty_iff {h k r : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> Cont h k r ->
      (hsame r BHist.Empty ↔ hsame h BHist.Empty ∧ hsame k BHist.Empty) := by
  intro carrierH carrierK continuation
  constructor
  · intro resultEmpty
    cases carrierH with
    | inl emptyH =>
        cases carrierK with
        | inl emptyK =>
            exact And.intro emptyH emptyK
        | inr ratK =>
            have sameRK : hsame r k :=
              cont_respects_hsame emptyH (hsame_refl k) continuation (cont_left_unit k)
            exact False.elim
              (RatHistoryCarrier_not_empty ratK (hsame_trans (hsame_symm sameRK) resultEmpty))
    | inr ratH =>
        cases carrierK with
        | inl emptyK =>
            have sameRH : hsame r h :=
              cont_respects_hsame (hsame_refl h) emptyK continuation (cont_right_unit h)
            exact False.elim
              (RatHistoryCarrier_not_empty ratH (hsame_trans (hsame_symm sameRH) resultEmpty))
        | inr ratK =>
            have resultCarrier : RatHistoryCarrier r :=
              field_rat_denominator_continuation_carrier_closure ratH ratK continuation
            exact False.elim (RatHistoryCarrier_not_empty resultCarrier resultEmpty)
  · intro endpoints
    exact cont_respects_hsame endpoints.left endpoints.right continuation
      (cont_left_unit BHist.Empty)

end BEDC.Derived.FieldUp
