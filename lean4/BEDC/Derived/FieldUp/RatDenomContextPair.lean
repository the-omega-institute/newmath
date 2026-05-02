import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatDenomContextPair_product_strict_support_iff {l r l' r' : BHist} :
    RatDenomUnitCarrier l -> RatDenomUnitCarrier r -> RatDenomUnitCarrier l' ->
      RatDenomUnitCarrier r' ->
        (RatHistoryCarrier (append (append l' l) (append r r')) <->
          RatHistoryCarrier l' ∨ RatHistoryCarrier l ∨ RatHistoryCarrier r ∨
            RatHistoryCarrier r') := by
  intro carrierL carrierR carrierL' carrierR'
  have carrierRR' : RatDenomUnitCarrier (append r r') :=
    RatDenomUnitCarrier_continuation_closed carrierR carrierR' (cont_intro rfl)
  have leftSupport :
      RatHistoryCarrier (append (append l' l) (append r r')) <->
        RatHistoryCarrier l' ∨ RatHistoryCarrier l ∨ RatHistoryCarrier (append r r') :=
    field_rat_denominator_empty_unit_bilateral_multiplication_support_exactness carrierL
      carrierL' carrierRR'
  have rightSupport :
      RatHistoryCarrier (append r r') <->
        RatHistoryCarrier r ∨ RatHistoryCarrier r' := by
    have nonemptyIff :=
      field_rat_denominator_empty_unit_product_nonempty_iff carrierR carrierR'
    constructor
    · intro ratRR'
      exact Iff.mp nonemptyIff (RatHistoryCarrier_not_empty ratRR')
    · intro strictSupport
      have nonemptyRR' : hsame (append r r') BHist.Empty -> False :=
        Iff.mpr nonemptyIff strictSupport
      exact RatDenomUnitCarrier_nonempty_rat carrierRR' nonemptyRR'
  constructor
  · intro productCarrier
    have support := Iff.mp leftSupport productCarrier
    cases support with
    | inl ratL' =>
        exact Or.inl ratL'
    | inr tailSupport =>
        cases tailSupport with
        | inl ratL =>
            exact Or.inr (Or.inl ratL)
        | inr ratRR' =>
            have rightStrict := Iff.mp rightSupport ratRR'
            cases rightStrict with
            | inl ratR =>
                exact Or.inr (Or.inr (Or.inl ratR))
            | inr ratR' =>
                exact Or.inr (Or.inr (Or.inr ratR'))
  · intro strictSupport
    have leftStrict :
        RatHistoryCarrier l' ∨ RatHistoryCarrier l ∨ RatHistoryCarrier (append r r') := by
      cases strictSupport with
      | inl ratL' =>
          exact Or.inl ratL'
      | inr tailSupport =>
          cases tailSupport with
          | inl ratL =>
              exact Or.inr (Or.inl ratL)
          | inr rightStrict =>
              exact Or.inr (Or.inr (Iff.mpr rightSupport rightStrict))
    exact Iff.mpr leftSupport leftStrict

theorem RatDenomContextPair_product_strict_support_transport
    {l r l' r' s t s' t' : BHist} :
    RatDenomUnitClassifier l s -> RatDenomUnitClassifier r t ->
      RatDenomUnitClassifier l' s' -> RatDenomUnitClassifier r' t' ->
        (RatHistoryCarrier (append (append l' l) (append r r')) <->
          RatHistoryCarrier (append (append s' s) (append t t'))) := by
  intro classifiedL classifiedR classifiedL' classifiedR'
  have sameLeft : hsame (append l' l) (append s' s) :=
    cont_respects_hsame classifiedL'.right.right classifiedL.right.right
      (cont_intro rfl) (cont_intro rfl)
  have sameRight : hsame (append r r') (append t t') :=
    cont_respects_hsame classifiedR.right.right classifiedR'.right.right
      (cont_intro rfl) (cont_intro rfl)
  have sameProduct :
      hsame (append (append l' l) (append r r')) (append (append s' s) (append t t')) :=
    cont_respects_hsame sameLeft sameRight (cont_intro rfl) (cont_intro rfl)
  constructor
  · intro productCarrier
    exact RatHistoryCarrier_hsame_transport sameProduct productCarrier
  · intro productCarrier
    exact RatHistoryCarrier_hsame_transport (hsame_symm sameProduct) productCarrier

end BEDC.Derived.FieldUp
