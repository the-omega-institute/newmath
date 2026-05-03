import BEDC.Derived.FieldUp.RatDenomUnit
import BEDC.Derived.FieldUp.PositiveDenominatorAppendSplit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
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

theorem RatHistoryClassifier_append_right_denom_unit_closed {h h' k k' : BHist} :
    RatHistoryClassifier h h' -> RatDenomUnitClassifier k k' ->
      RatHistoryClassifier (append h k) (append h' k') := by
  intro classifiedH classifiedK
  have carrierLeft : RatHistoryCarrier (append h k) :=
    RatDenomUnitCarrier_append_left_rat_closed classifiedH.left classifiedK.left
  have carrierRight : RatHistoryCarrier (append h' k') :=
    RatDenomUnitCarrier_append_left_rat_closed classifiedH.right.left classifiedK.right.left
  have sameAppend : hsame (append h k) (append h' k') :=
    cont_respects_hsame classifiedH.right.right classifiedK.right.right (cont_intro rfl)
      (cont_intro rfl)
  exact And.intro carrierLeft (And.intro carrierRight sameAppend)

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

theorem RatDenomUnitCarrier_append_factor_carriers {h k : BHist} :
    RatDenomUnitCarrier (append h k) -> RatDenomUnitCarrier h ∧ RatDenomUnitCarrier k := by
  intro productCarrier
  cases productCarrier with
  | inl productEmpty =>
      have parts := append_eq_empty_iff.mp productEmpty
      exact And.intro (Or.inl parts.left) (Or.inl parts.right)
  | inr productRat =>
      have productPositive : PositiveUnaryDenominator (append h k) :=
        RatHistoryCarrier_iff_positive_denominator.mp productRat
      have productUnary : UnaryHistory (append h k) :=
        (PositiveUnaryDenominator_unary_and_nonempty productPositive).left
      have hUnary : UnaryHistory h := unary_append_left_factor productUnary
      have kUnary : UnaryHistory k := unary_append_right_factor productUnary
      constructor
      · cases unary_history_cases hUnary with
        | inl hEmpty =>
            exact Or.inl hEmpty
        | inr hVisible =>
            cases hVisible with
            | intro tail tailData =>
                cases tailData with
                | intro hEq tailUnary =>
                    cases hEq
                    exact Or.inr
                      (RatHistoryCarrier_iff_positive_denominator.mpr
                        (PositiveUnaryDenominator_e1_iff_unary.mpr tailUnary))
      · cases unary_history_cases kUnary with
        | inl kEmpty =>
            exact Or.inl kEmpty
        | inr kVisible =>
            cases kVisible with
            | intro tail tailData =>
                cases tailData with
                | intro kEq tailUnary =>
                    cases kEq
                    exact Or.inr
                      (RatHistoryCarrier_iff_positive_denominator.mpr
                        (PositiveUnaryDenominator_e1_iff_unary.mpr tailUnary))

theorem RatDenomUnitClassifier_append_context_cancel_iff {L R Q S : BHist} :
    RatDenomUnitClassifier L R ->
      (RatDenomUnitClassifier (append Q L) (append S R) <->
        RatDenomUnitClassifier Q S) := by
  intro suffixClassified
  constructor
  · intro classified
    have leftFactors := RatDenomUnitCarrier_append_factor_carriers classified.left
    have rightFactors := RatDenomUnitCarrier_append_factor_carriers classified.right.left
    have sameRightSuffix : hsame (append S R) (append S L) :=
      hsame_symm (congrArg (append S) suffixClassified.right.right)
    have sameWithSharedSuffix : hsame (append Q L) (append S L) :=
      hsame_trans classified.right.right sameRightSuffix
    exact ⟨leftFactors.left, rightFactors.left, append_right_cancel sameWithSharedSuffix⟩
  · intro classified
    have leftCarrier : RatDenomUnitCarrier (append Q L) :=
      RatDenomUnitCarrier_continuation_closed classified.left suffixClassified.left (cont_intro rfl)
    have rightCarrier : RatDenomUnitCarrier (append S R) :=
      RatDenomUnitCarrier_continuation_closed classified.right.left suffixClassified.right.left
        (cont_intro rfl)
    cases classified.right.right
    cases suffixClassified.right.right
    exact ⟨leftCarrier, rightCarrier, hsame_refl (append Q L)⟩

end BEDC.Derived.FieldUp
