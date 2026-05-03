import BEDC.Derived.FieldUp.ContextualAction
import BEDC.Derived.FieldUp.RatDenomContextPair

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

theorem ratup_fieldup_transported_strict_support_contextual_singleton_exclusion
    {p q p' q' h l r l' r' s t s' t' ctx : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitClassifier l s ->
        RatDenomUnitClassifier r t -> RatDenomUnitClassifier l' s' ->
          RatDenomUnitClassifier r' t' ->
            RatHistoryCarrier
              (RatDenomUnitContextualAction p' q' l' r'
                (RatDenomUnitContextualAction p q l r h)) ->
            (fieldSingletonEmptyCarrier
              (append ctx
                (RatDenomUnitContextualAction p' q' s' t'
                  (RatDenomUnitContextualAction p q s t h))) -> False) ∧
            (fieldSingletonEmptyCarrier
              (append
                (RatDenomUnitContextualAction p' q' s' t'
                  (RatDenomUnitContextualAction p q s t h)) ctx) -> False) := by
  intro sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
    leftStrict
  have endpoint :=
    ratup_fieldup_transported_strict_support_non_singleton
      sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
      leftStrict
  exact ⟨
    (fun singleton =>
      fieldSingletonEmptyCarrier_append_ratHistoryCarrier_absurd singleton endpoint.right.left),
    (fun singleton =>
      fieldSingletonEmptyCarrier_append_left_ratHistoryCarrier_absurd singleton
        endpoint.right.left)⟩

theorem ratup_fieldup_transported_strict_support_separation_package
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
                (RatDenomUnitContextualAction p q s t h)) -> False) ∧
            (hsame
              (RatDenomUnitContextualAction p' q' s' t'
                (RatDenomUnitContextualAction p q s t h)) BHist.Empty -> False) := by
  intro sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
    leftStrict
  have endpoint :=
    ratup_fieldup_transported_strict_support_non_singleton
      sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
      leftStrict
  exact ⟨endpoint.left, endpoint.right.left, endpoint.right.right,
    fun sameEmpty => RatHistoryCarrier_not_empty endpoint.right.left sameEmpty⟩

theorem ratup_fieldup_transported_strict_support_contextual_nonzero_package
    {p q p' q' h l r l' r' s t s' t' ctx : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitClassifier l s ->
        RatDenomUnitClassifier r t -> RatDenomUnitClassifier l' s' ->
          RatDenomUnitClassifier r' t' ->
            RatHistoryCarrier
              (RatDenomUnitContextualAction p' q' l' r'
                (RatDenomUnitContextualAction p q l r h)) ->
            fieldSingletonEmptyNonZero
              (append ctx
                (RatDenomUnitContextualAction p' q' s' t'
                  (RatDenomUnitContextualAction p q s t h))) ∧
            fieldSingletonEmptyNonZero
              (append
                (RatDenomUnitContextualAction p' q' s' t'
                  (RatDenomUnitContextualAction p q s t h)) ctx) := by
  intro sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
    leftStrict
  have contextualReject :=
    ratup_fieldup_transported_strict_support_contextual_singleton_exclusion
      (ctx := ctx)
      sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
      leftStrict
  constructor
  · intro singleton
    exact contextualReject.left singleton.left
  · intro singleton
    exact contextualReject.right singleton.left

theorem ratup_fieldup_transported_strict_support_singleton_classifier_exclusion
    {p q p' q' h l r l' r' s t s' t' L R : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitClassifier l s ->
        RatDenomUnitClassifier r t -> RatDenomUnitClassifier l' s' ->
          RatDenomUnitClassifier r' t' ->
            RatHistoryCarrier
              (RatDenomUnitContextualAction p' q' l' r'
                (RatDenomUnitContextualAction p q l r h)) ->
            fieldSingletonEmptyClassifier
              (append L
                (RatDenomUnitContextualAction p' q' s' t'
                  (RatDenomUnitContextualAction p q s t h)))
              (append R
                (RatDenomUnitContextualAction p' q' s' t'
                  (RatDenomUnitContextualAction p q s t h))) -> False := by
  intro sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
    leftStrict singleton
  have supportTransport :=
    field_rat_denominator_contextual_action_pair_transport_support
      sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
  have transportedStrict :
      RatHistoryCarrier
        (RatDenomUnitContextualAction p' q' s' t'
          (RatDenomUnitContextualAction p q s t h)) :=
    Iff.mp supportTransport leftStrict
  have transportedClassifier :
      RatHistoryClassifier
        (RatDenomUnitContextualAction p' q' s' t'
          (RatDenomUnitContextualAction p q s t h))
        (RatDenomUnitContextualAction p' q' s' t'
          (RatDenomUnitContextualAction p q s t h)) :=
    ⟨transportedStrict, transportedStrict, hsame_refl _⟩
  exact fieldSingletonEmptyClassifier_append_RatHistoryClassifier_absurd
    transportedClassifier singleton

theorem RatDenomUnitContextualAction_nested_pair_action_coherence
    {h l0 r0 l1 r1 l2 r2 : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier l0 -> RatDenomUnitCarrier r0 ->
      RatDenomUnitCarrier l1 -> RatDenomUnitCarrier r1 -> RatDenomUnitCarrier l2 ->
        RatDenomUnitCarrier r2 ->
          RatDenomUnitCarrier
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
              (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
                (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h))) ∧
          RatDenomUnitClassifier
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
              (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
                (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h)))
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty
              (append l2 (append l1 l0)) (append (append r0 r1) r2) h) := by
  intro carrierH carrierL0 carrierR0 carrierL1 carrierR1 carrierL2 carrierR2
  have firstLaws :=
    field_rat_denominator_contextual_action_composition_support_laws
      (hsame_refl BHist.Empty) (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
      (hsame_refl BHist.Empty) carrierH carrierL0 carrierR0 carrierL1 carrierR1
  have carrierL10 : RatDenomUnitCarrier (append l1 l0) :=
    RatDenomUnitCarrier_continuation_closed carrierL1 carrierL0 (cont_intro rfl)
  have carrierR01 : RatDenomUnitCarrier (append r0 r1) :=
    RatDenomUnitCarrier_continuation_closed carrierR0 carrierR1 (cont_intro rfl)
  have finalLaws :=
    field_rat_denominator_contextual_action_composition_support_laws
      (hsame_refl BHist.Empty) (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
      (hsame_refl BHist.Empty) carrierH carrierL10 carrierR01 carrierL2 carrierR2
  have sameInner :
      hsame
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h))
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty (append l1 l0)
          (append r0 r1) h) :=
    firstLaws.right.left.right.right
  have sameNested :
      hsame
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h)))
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty (append l1 l0)
            (append r0 r1) h)) :=
    congrArg (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2) sameInner
  have carrierNested : RatDenomUnitCarrier
      (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h))) :=
    RatDenomUnitCarrier_hsame_transport (hsame_symm sameNested) finalLaws.left
  have carrierTarget : RatDenomUnitCarrier
      (RatDenomUnitContextualAction BHist.Empty BHist.Empty
        (append l2 (append l1 l0)) (append (append r0 r1) r2) h) :=
    finalLaws.right.left.right.left
  have sameTarget :
      hsame
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h)))
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty
          (append l2 (append l1 l0)) (append (append r0 r1) r2) h) :=
    hsame_trans sameNested finalLaws.right.left.right.right
  exact ⟨carrierNested, carrierNested, carrierTarget, sameTarget⟩

end BEDC.Derived.FieldUp
