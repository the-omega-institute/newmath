import BEDC.Derived.FieldUp.ContextualAction

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatDenomUnitContextualAction_normalized_pair_singleton_classifier_exclusion
    {p q p1 q1 h l r l1 r1 L R : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p1 BHist.Empty ->
      hsame q1 BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitCarrier l ->
        RatDenomUnitCarrier r -> RatDenomUnitCarrier l1 -> RatDenomUnitCarrier r1 ->
          RatHistoryCarrier h ->
            fieldSingletonEmptyClassifier
              (append L
                (RatDenomUnitContextualAction p1 q1 l1 r1
                  (RatDenomUnitContextualAction p q l r h)))
              (append R
                (RatDenomUnitContextualAction p1 q1 (append l1 l) (append r r1) h)) ->
              False := by
  intro sameP sameQ sameP1 sameQ1 carrierH carrierL carrierR carrierL1 carrierR1 ratH
    singleton
  have laws :=
    field_rat_denominator_contextual_action_composition_support_laws sameP sameQ sameP1
      sameQ1 carrierH carrierL carrierR carrierL1 carrierR1
  let nested :=
    RatDenomUnitContextualAction p1 q1 l1 r1
      (RatDenomUnitContextualAction p q l r h)
  let normalized :=
    RatDenomUnitContextualAction p1 q1 (append l1 l) (append r r1) h
  have nestedRat : RatHistoryCarrier nested :=
    Iff.mpr laws.right.right (Or.inr (Or.inr (Or.inl ratH)))
  have sameNestedNormalized : hsame nested normalized :=
    laws.right.left.right.right
  have normalizedRat : RatHistoryCarrier normalized :=
    RatHistoryCarrier_hsame_transport sameNestedNormalized nestedRat
  have ratClassifier : RatHistoryClassifier nested normalized :=
    And.intro nestedRat (And.intro normalizedRat sameNestedNormalized)
  exact fieldSingletonEmptyClassifier_append_RatHistoryClassifier_absurd ratClassifier singleton

end BEDC.Derived.FieldUp
