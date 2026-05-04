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

theorem RatDenomUnitClassifier_continuation_result_empty_iff {h h' k k' r r' : BHist} :
    RatDenomUnitClassifier h h' -> RatDenomUnitClassifier k k' -> Cont h k r ->
      Cont h' k' r' -> (hsame r BHist.Empty ↔ hsame r' BHist.Empty) := by
  intro classifiedH classifiedK continuation continuation'
  have leftResult :
      hsame r BHist.Empty ↔ hsame h BHist.Empty ∧ hsame k BHist.Empty :=
    RatDenomUnitCarrier_continuation_result_empty_iff classifiedH.left classifiedK.left
      continuation
  have rightResult :
      hsame r' BHist.Empty ↔ hsame h' BHist.Empty ∧ hsame k' BHist.Empty :=
    RatDenomUnitCarrier_continuation_result_empty_iff classifiedH.right.left
      classifiedK.right.left continuation'
  constructor
  · intro resultEmpty
    have endpoints := leftResult.mp resultEmpty
    have endpoints' : hsame h' BHist.Empty ∧ hsame k' BHist.Empty :=
      And.intro
        (hsame_trans (hsame_symm classifiedH.right.right) endpoints.left)
        (hsame_trans (hsame_symm classifiedK.right.right) endpoints.right)
    exact rightResult.mpr endpoints'
  · intro resultEmpty'
    have endpoints' := rightResult.mp resultEmpty'
    have endpoints : hsame h BHist.Empty ∧ hsame k BHist.Empty :=
      And.intro
        (hsame_trans classifiedH.right.right endpoints'.left)
        (hsame_trans classifiedK.right.right endpoints'.right)
    exact leftResult.mpr endpoints

end BEDC.Derived.FieldUp
