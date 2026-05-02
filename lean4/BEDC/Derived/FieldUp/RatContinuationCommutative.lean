import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_empty_unit_continuation_commutative_monoid_laws :
    (RatDenomUnitCarrier BHist.Empty ∧
      (∀ {h k : BHist}, RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
        RatDenomUnitCarrier (append h k)) ∧
      (∀ {h : BHist}, RatDenomUnitCarrier h ->
        RatDenomUnitClassifier (append BHist.Empty h) h ∧
          RatDenomUnitClassifier (append h BHist.Empty) h) ∧
      (∀ {h k l : BHist}, RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
        RatDenomUnitCarrier l ->
          RatDenomUnitClassifier (append (append h k) l) (append h (append k l))) ∧
      (∀ {h h' k k' : BHist}, RatDenomUnitClassifier h h' ->
        RatDenomUnitClassifier k k' ->
          RatDenomUnitClassifier (append h k) (append h' k'))) ∧
    (∀ {h k : BHist}, RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
      RatDenomUnitClassifier (append h k) (append k h)) := by
  constructor
  · exact field_rat_denominator_empty_unit_continuation_monoid_laws
  · intro h k carrierH carrierK
    have carrierHK : RatDenomUnitCarrier (append h k) :=
      RatDenomUnitCarrier_continuation_closed carrierH carrierK (cont_intro rfl)
    have carrierKH : RatDenomUnitCarrier (append k h) :=
      RatDenomUnitCarrier_continuation_closed carrierK carrierH (cont_intro rfl)
    have sameHK : hsame (append h k) (append k h) := by
      cases carrierH with
      | inl emptyH =>
          cases carrierK with
          | inl emptyK =>
              exact hsame_trans
                (append_eq_empty_iff.mpr (And.intro emptyH emptyK))
                (hsame_symm (append_eq_empty_iff.mpr (And.intro emptyK emptyH)))
          | inr ratK =>
              have leftSame : hsame (append h k) k :=
                cont_respects_hsame emptyH (hsame_refl k) (cont_intro rfl)
                  (cont_left_unit k)
              have rightSame : hsame (append k h) k :=
                cont_respects_hsame (hsame_refl k) emptyH (cont_intro rfl)
                  (cont_right_unit k)
              exact hsame_trans leftSame (hsame_symm rightSame)
      | inr ratH =>
          cases carrierK with
          | inl emptyK =>
              have leftSame : hsame (append h k) h :=
                cont_respects_hsame (hsame_refl h) emptyK (cont_intro rfl)
                  (cont_right_unit h)
              have rightSame : hsame (append k h) h :=
                cont_respects_hsame emptyK (hsame_refl h) (cont_intro rfl)
                  (cont_left_unit h)
              exact hsame_trans leftSame (hsame_symm rightSame)
          | inr ratK =>
              exact
                (field_rat_denominator_continuation_commutative_classifier ratH ratK
                  (cont_intro rfl) (cont_intro rfl)).right.right
    exact And.intro carrierHK (And.intro carrierKH sameHK)

end BEDC.Derived.FieldUp
