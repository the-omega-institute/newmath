import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatDenomUnitClassifier_append_comm {h k : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
      RatDenomUnitClassifier (append h k) (append k h) := by
  intro carrierH carrierK
  have carrierHK : RatDenomUnitCarrier (append h k) :=
    RatDenomUnitCarrier_continuation_closed carrierH carrierK (cont_intro rfl)
  have carrierKH : RatDenomUnitCarrier (append k h) :=
    RatDenomUnitCarrier_continuation_closed carrierK carrierH (cont_intro rfl)
  constructor
  · exact carrierHK
  constructor
  · exact carrierKH
  cases carrierH with
  | inl emptyH =>
      cases carrierK with
      | inl emptyK =>
          have sameHKEmpty : hsame (append h k) BHist.Empty :=
            cont_respects_hsame emptyH emptyK (cont_intro rfl) (cont_left_unit BHist.Empty)
          have sameKHEmpty : hsame (append k h) BHist.Empty :=
            cont_respects_hsame emptyK emptyH (cont_intro rfl) (cont_left_unit BHist.Empty)
          exact hsame_trans sameHKEmpty (hsame_symm sameKHEmpty)
      | inr ratK =>
          have sameHKK : hsame (append h k) k :=
            cont_respects_hsame emptyH (hsame_refl k) (cont_intro rfl) (cont_left_unit k)
          have sameKHK : hsame (append k h) k :=
            cont_respects_hsame (hsame_refl k) emptyH (cont_intro rfl) (cont_right_unit k)
          exact hsame_trans sameHKK (hsame_symm sameKHK)
  | inr ratH =>
      cases carrierK with
      | inl emptyK =>
          have sameHKH : hsame (append h k) h :=
            cont_respects_hsame (hsame_refl h) emptyK (cont_intro rfl) (cont_right_unit h)
          have sameKHH : hsame (append k h) h :=
            cont_respects_hsame emptyK (hsame_refl h) (cont_intro rfl) (cont_left_unit h)
          exact hsame_trans sameHKH (hsame_symm sameKHH)
      | inr ratK =>
          exact (field_rat_denominator_continuation_commutative_classifier ratH ratK
            (cont_intro rfl) (cont_intro rfl)).right.right

theorem RatDenomUnitClassifier_append_comm_congr {h h' k k' : BHist} :
    RatDenomUnitClassifier h h' -> RatDenomUnitClassifier k k' ->
      RatDenomUnitClassifier (append h k) (append k' h') := by
  intro classifiedH classifiedK
  have straight : RatDenomUnitClassifier (append h k) (append h' k') :=
    RatDenomUnitClassifier_continuation_closed classifiedH classifiedK (cont_intro rfl)
      (cont_intro rfl)
  have swapped : RatDenomUnitClassifier (append h' k') (append k' h') :=
    RatDenomUnitClassifier_append_comm classifiedH.right.left classifiedK.right.left
  exact And.intro straight.left
    (And.intro swapped.right.left (hsame_trans straight.right.right swapped.right.right))

end BEDC.Derived.FieldUp
