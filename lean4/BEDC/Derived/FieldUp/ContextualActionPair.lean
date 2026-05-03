import BEDC.Derived.FieldUp.ContextualAction
import BEDC.Derived.FieldUp.RatDenomContextPair

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp

theorem field_rat_denominator_contextual_action_pair_transport_support
    {p q p' q' h l r l' r' s t s' t' : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitClassifier l s ->
        RatDenomUnitClassifier r t -> RatDenomUnitClassifier l' s' ->
          RatDenomUnitClassifier r' t' ->
            (RatHistoryCarrier
              (RatDenomUnitContextualAction p' q' l' r'
                (RatDenomUnitContextualAction p q l r h)) <->
              RatHistoryCarrier
                (RatDenomUnitContextualAction p' q' s' t'
                  (RatDenomUnitContextualAction p q s t h))) := by
  intro sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
  have leftLaws :=
    field_rat_denominator_contextual_action_composition_support_laws
      sameP sameQ sameP' sameQ' carrierH classifiedL.left classifiedR.left
      classifiedL'.left classifiedR'.left
  have rightLaws :=
    field_rat_denominator_contextual_action_composition_support_laws
      sameP sameQ sameP' sameQ' carrierH classifiedL.right.left classifiedR.right.left
      classifiedL'.right.left classifiedR'.right.left
  have contextTransport :
      (RatHistoryCarrier l' ∨ RatHistoryCarrier l ∨ RatHistoryCarrier r ∨
          RatHistoryCarrier r') <->
        RatHistoryCarrier s' ∨ RatHistoryCarrier s ∨ RatHistoryCarrier t ∨
          RatHistoryCarrier t' := by
    have leftSupport :=
      RatDenomContextPair_product_strict_support_iff classifiedL.left classifiedR.left
        classifiedL'.left classifiedR'.left
    have rightSupport :=
      RatDenomContextPair_product_strict_support_iff classifiedL.right.left
        classifiedR.right.left classifiedL'.right.left classifiedR'.right.left
    have productTransport :=
      RatDenomContextPair_product_strict_support_transport classifiedL classifiedR classifiedL'
        classifiedR'
    constructor
    · intro support
      exact Iff.mp rightSupport (Iff.mp productTransport (Iff.mpr leftSupport support))
    · intro support
      exact Iff.mp leftSupport (Iff.mpr productTransport (Iff.mpr rightSupport support))
  have supportTransport :
      (RatHistoryCarrier l' ∨ RatHistoryCarrier l ∨ RatHistoryCarrier h ∨
          RatHistoryCarrier r ∨ RatHistoryCarrier r') <->
        RatHistoryCarrier s' ∨ RatHistoryCarrier s ∨ RatHistoryCarrier h ∨
          RatHistoryCarrier t ∨ RatHistoryCarrier t' := by
    constructor
    · intro support
      cases support with
      | inl ratL' =>
          have contextRight := Iff.mp contextTransport (Or.inl ratL')
          cases contextRight with
          | inl ratS' => exact Or.inl ratS'
          | inr tail =>
              cases tail with
              | inl ratS => exact Or.inr (Or.inl ratS)
              | inr rightTail =>
                  cases rightTail with
                  | inl ratT => exact Or.inr (Or.inr (Or.inr (Or.inl ratT)))
                  | inr ratT' => exact Or.inr (Or.inr (Or.inr (Or.inr ratT')))
      | inr tail =>
          cases tail with
          | inl ratL =>
              have contextRight := Iff.mp contextTransport (Or.inr (Or.inl ratL))
              cases contextRight with
              | inl ratS' => exact Or.inl ratS'
              | inr rightTail =>
                  cases rightTail with
                  | inl ratS => exact Or.inr (Or.inl ratS)
                  | inr rightTail =>
                      cases rightTail with
                      | inl ratT => exact Or.inr (Or.inr (Or.inr (Or.inl ratT)))
                      | inr ratT' => exact Or.inr (Or.inr (Or.inr (Or.inr ratT')))
          | inr tail =>
              cases tail with
              | inl ratH => exact Or.inr (Or.inr (Or.inl ratH))
              | inr tail =>
                  cases tail with
                  | inl ratR =>
                      have contextRight :=
                        Iff.mp contextTransport (Or.inr (Or.inr (Or.inl ratR)))
                      cases contextRight with
                      | inl ratS' => exact Or.inl ratS'
                      | inr rightTail =>
                          cases rightTail with
                          | inl ratS => exact Or.inr (Or.inl ratS)
                          | inr rightTail =>
                              cases rightTail with
                              | inl ratT => exact Or.inr (Or.inr (Or.inr (Or.inl ratT)))
                              | inr ratT' => exact Or.inr (Or.inr (Or.inr (Or.inr ratT')))
                  | inr ratR' =>
                      have contextRight :=
                        Iff.mp contextTransport (Or.inr (Or.inr (Or.inr ratR')))
                      cases contextRight with
                      | inl ratS' => exact Or.inl ratS'
                      | inr rightTail =>
                          cases rightTail with
                          | inl ratS => exact Or.inr (Or.inl ratS)
                          | inr rightTail =>
                              cases rightTail with
                              | inl ratT => exact Or.inr (Or.inr (Or.inr (Or.inl ratT)))
                              | inr ratT' => exact Or.inr (Or.inr (Or.inr (Or.inr ratT')))
    · intro support
      cases support with
      | inl ratS' =>
          have contextLeft := Iff.mpr contextTransport (Or.inl ratS')
          cases contextLeft with
          | inl ratL' => exact Or.inl ratL'
          | inr tail =>
              cases tail with
              | inl ratL => exact Or.inr (Or.inl ratL)
              | inr rightTail =>
                  cases rightTail with
                  | inl ratR => exact Or.inr (Or.inr (Or.inr (Or.inl ratR)))
                  | inr ratR' => exact Or.inr (Or.inr (Or.inr (Or.inr ratR')))
      | inr tail =>
          cases tail with
          | inl ratS =>
              have contextLeft := Iff.mpr contextTransport (Or.inr (Or.inl ratS))
              cases contextLeft with
              | inl ratL' => exact Or.inl ratL'
              | inr rightTail =>
                  cases rightTail with
                  | inl ratL => exact Or.inr (Or.inl ratL)
                  | inr rightTail =>
                      cases rightTail with
                      | inl ratR => exact Or.inr (Or.inr (Or.inr (Or.inl ratR)))
                      | inr ratR' => exact Or.inr (Or.inr (Or.inr (Or.inr ratR')))
          | inr tail =>
              cases tail with
              | inl ratH => exact Or.inr (Or.inr (Or.inl ratH))
              | inr tail =>
                  cases tail with
                  | inl ratT =>
                      have contextLeft :=
                        Iff.mpr contextTransport (Or.inr (Or.inr (Or.inl ratT)))
                      cases contextLeft with
                      | inl ratL' => exact Or.inl ratL'
                      | inr rightTail =>
                          cases rightTail with
                          | inl ratL => exact Or.inr (Or.inl ratL)
                          | inr rightTail =>
                              cases rightTail with
                              | inl ratR => exact Or.inr (Or.inr (Or.inr (Or.inl ratR)))
                              | inr ratR' => exact Or.inr (Or.inr (Or.inr (Or.inr ratR')))
                  | inr ratT' =>
                      have contextLeft :=
                        Iff.mpr contextTransport (Or.inr (Or.inr (Or.inr ratT')))
                      cases contextLeft with
                      | inl ratL' => exact Or.inl ratL'
                      | inr rightTail =>
                          cases rightTail with
                          | inl ratL => exact Or.inr (Or.inl ratL)
                          | inr rightTail =>
                              cases rightTail with
                              | inl ratR => exact Or.inr (Or.inr (Or.inr (Or.inl ratR)))
                              | inr ratR' => exact Or.inr (Or.inr (Or.inr (Or.inr ratR')))
  constructor
  · intro leftCarrier
    exact Iff.mpr rightLaws.right.right
      (Iff.mp supportTransport (Iff.mp leftLaws.right.right leftCarrier))
  · intro rightCarrier
    exact Iff.mpr leftLaws.right.right
      (Iff.mpr supportTransport (Iff.mp rightLaws.right.right rightCarrier))

theorem field_rat_denominator_contextual_action_pair_transport_carrier_support
    {p q p' q' h l r l' r' s t s' t' : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitClassifier l s ->
        RatDenomUnitClassifier r t -> RatDenomUnitClassifier l' s' ->
          RatDenomUnitClassifier r' t' ->
            RatDenomUnitCarrier
              (RatDenomUnitContextualAction p' q' l' r'
                (RatDenomUnitContextualAction p q l r h)) ∧
            RatDenomUnitCarrier
              (RatDenomUnitContextualAction p' q' s' t'
                (RatDenomUnitContextualAction p q s t h)) ∧
            (RatHistoryCarrier
              (RatDenomUnitContextualAction p' q' l' r'
                (RatDenomUnitContextualAction p q l r h)) <->
              RatHistoryCarrier
                (RatDenomUnitContextualAction p' q' s' t'
                  (RatDenomUnitContextualAction p q s t h))) := by
  intro sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
  have leftLaws :=
    field_rat_denominator_contextual_action_composition_support_laws
      sameP sameQ sameP' sameQ' carrierH classifiedL.left classifiedR.left
      classifiedL'.left classifiedR'.left
  have rightLaws :=
    field_rat_denominator_contextual_action_composition_support_laws
      sameP sameQ sameP' sameQ' carrierH classifiedL.right.left classifiedR.right.left
      classifiedL'.right.left classifiedR'.right.left
  exact ⟨leftLaws.left, rightLaws.left,
    field_rat_denominator_contextual_action_pair_transport_support
      sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'⟩

theorem ratup_fieldup_transported_strict_support_non_singleton
    {p q p' q' h l r l' r' s t s' t' : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitClassifier l s ->
        RatDenomUnitClassifier r t -> RatDenomUnitClassifier l' s' ->
          RatDenomUnitClassifier r' t' ->
            RatHistoryCarrier
              (RatDenomUnitContextualAction p' q' l' r'
                (RatDenomUnitContextualAction p q l r h)) ->
            RatDenomUnitCarrier
              (RatDenomUnitContextualAction p' q' s' t'
                (RatDenomUnitContextualAction p q s t h)) ∧
            RatHistoryCarrier
              (RatDenomUnitContextualAction p' q' s' t'
                (RatDenomUnitContextualAction p q s t h)) ∧
            (fieldSingletonEmptyCarrier
              (RatDenomUnitContextualAction p' q' s' t'
                (RatDenomUnitContextualAction p q s t h)) -> False) := by
  intro sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
    leftStrict
  have transported :=
    field_rat_denominator_contextual_action_pair_transport_carrier_support
      sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
  have rightStrict : RatHistoryCarrier
      (RatDenomUnitContextualAction p' q' s' t'
        (RatDenomUnitContextualAction p q s t h)) :=
    Iff.mp transported.right.right leftStrict
  exact ⟨transported.right.left, rightStrict,
    fun singleton => RatHistoryCarrier_not_empty rightStrict singleton⟩

end BEDC.Derived.FieldUp
