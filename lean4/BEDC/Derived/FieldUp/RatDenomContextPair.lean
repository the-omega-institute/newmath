import BEDC.Derived.FieldUp.RatDenomUnit
import BEDC.Derived.FieldUp.RatContinuationAppendComm

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

theorem RatDenomContextPair_operation_stability {l r m s l' r' m' s' : BHist} :
    RatDenomUnitClassifier l m -> RatDenomUnitClassifier r s ->
      RatDenomUnitClassifier l' m' -> RatDenomUnitClassifier r' s' ->
        RatDenomUnitCarrier (append l' l) ∧ RatDenomUnitCarrier (append r r') ∧
          RatDenomUnitCarrier (append m' m) ∧ RatDenomUnitCarrier (append s s') ∧
          RatDenomUnitClassifier (append l' l) (append m' m) ∧
          RatDenomUnitClassifier (append r r') (append s s') ∧
          (RatHistoryCarrier (append (append l' l) (append r r')) <->
            (RatHistoryCarrier l ∨ RatHistoryCarrier r) ∨
              (RatHistoryCarrier l' ∨ RatHistoryCarrier r')) := by
  intro classifiedL classifiedR classifiedL' classifiedR'
  have carrierL'L : RatDenomUnitCarrier (append l' l) :=
    RatDenomUnitCarrier_continuation_closed classifiedL'.left classifiedL.left (cont_intro rfl)
  have carrierRR' : RatDenomUnitCarrier (append r r') :=
    RatDenomUnitCarrier_continuation_closed classifiedR.left classifiedR'.left (cont_intro rfl)
  have carrierM'M : RatDenomUnitCarrier (append m' m) :=
    RatDenomUnitCarrier_continuation_closed classifiedL'.right.left classifiedL.right.left
      (cont_intro rfl)
  have carrierSS' : RatDenomUnitCarrier (append s s') :=
    RatDenomUnitCarrier_continuation_closed classifiedR.right.left classifiedR'.right.left
      (cont_intro rfl)
  have sameLeft : hsame (append l' l) (append m' m) :=
    cont_respects_hsame classifiedL'.right.right classifiedL.right.right
      (cont_intro rfl) (cont_intro rfl)
  have sameRight : hsame (append r r') (append s s') :=
    cont_respects_hsame classifiedR.right.right classifiedR'.right.right
      (cont_intro rfl) (cont_intro rfl)
  have support :=
    RatDenomContextPair_product_strict_support_iff classifiedL.left classifiedR.left
      classifiedL'.left classifiedR'.left
  refine ⟨carrierL'L, carrierRR', carrierM'M, carrierSS',
    ⟨carrierL'L, carrierM'M, sameLeft⟩, ⟨carrierRR', carrierSS', sameRight⟩, ?_⟩
  constructor
  · intro productCarrier
    cases Iff.mp support productCarrier with
    | inl ratL' => exact Or.inr (Or.inl ratL')
    | inr tail =>
        cases tail with
        | inl ratL => exact Or.inl (Or.inl ratL)
        | inr rightTail =>
            cases rightTail with
            | inl ratR => exact Or.inl (Or.inr ratR)
            | inr ratR' => exact Or.inr (Or.inr ratR')
  · intro support'
    apply Iff.mpr support
    cases support' with
    | inl leftSupport =>
        cases leftSupport with
        | inl ratL => exact Or.inr (Or.inl ratL)
        | inr ratR => exact Or.inr (Or.inr (Or.inl ratR))
    | inr rightSupport =>
        cases rightSupport with
        | inl ratL' => exact Or.inl ratL'
        | inr ratR' => exact Or.inr (Or.inr (Or.inr ratR'))

theorem RatDenomContextPair_product_operation_stable {l r l' r' m s m' s' : BHist} :
    RatDenomUnitCarrier l -> RatDenomUnitCarrier r -> RatDenomUnitCarrier l' ->
      RatDenomUnitCarrier r' -> RatDenomUnitClassifier l m -> RatDenomUnitClassifier r s ->
        RatDenomUnitClassifier l' m' -> RatDenomUnitClassifier r' s' ->
          RatDenomUnitCarrier (append l' l) ∧ RatDenomUnitCarrier (append r r') ∧
            RatDenomUnitCarrier (append m' m) ∧ RatDenomUnitCarrier (append s s') ∧
              RatDenomUnitClassifier (append l' l) (append m' m) ∧
                RatDenomUnitClassifier (append r r') (append s s') ∧
                  (RatHistoryCarrier (append (append l' l) (append r r')) ↔
                    (RatHistoryCarrier l ∨ RatHistoryCarrier r) ∨
                      (RatHistoryCarrier l' ∨ RatHistoryCarrier r')) := by
  intro carrierL carrierR carrierL' carrierR' classifiedL classifiedR classifiedL' classifiedR'
  have carrierL'L : RatDenomUnitCarrier (append l' l) :=
    RatDenomUnitCarrier_continuation_closed carrierL' carrierL (cont_intro rfl)
  have carrierRR' : RatDenomUnitCarrier (append r r') :=
    RatDenomUnitCarrier_continuation_closed carrierR carrierR' (cont_intro rfl)
  have carrierM'M : RatDenomUnitCarrier (append m' m) :=
    RatDenomUnitCarrier_continuation_closed classifiedL'.right.left classifiedL.right.left
      (cont_intro rfl)
  have carrierSS' : RatDenomUnitCarrier (append s s') :=
    RatDenomUnitCarrier_continuation_closed classifiedR.right.left classifiedR'.right.left
      (cont_intro rfl)
  have classifiedLeft :
      RatDenomUnitClassifier (append l' l) (append m' m) :=
    RatDenomUnitClassifier_continuation_closed classifiedL' classifiedL
      (cont_intro rfl) (cont_intro rfl)
  have classifiedRight :
      RatDenomUnitClassifier (append r r') (append s s') :=
    RatDenomUnitClassifier_continuation_closed classifiedR classifiedR'
      (cont_intro rfl) (cont_intro rfl)
  have strictSupport :=
    RatDenomContextPair_product_strict_support_iff carrierL carrierR carrierL' carrierR'
  constructor
  · exact carrierL'L
  constructor
  · exact carrierRR'
  constructor
  · exact carrierM'M
  constructor
  · exact carrierSS'
  constructor
  · exact classifiedLeft
  constructor
  · exact classifiedRight
  constructor
  · intro productCarrier
    have support := Iff.mp strictSupport productCarrier
    cases support with
    | inl ratL' =>
        exact Or.inr (Or.inl ratL')
    | inr tailSupport =>
        cases tailSupport with
        | inl ratL =>
            exact Or.inl (Or.inl ratL)
        | inr rightSupport =>
            cases rightSupport with
            | inl ratR =>
                exact Or.inl (Or.inr ratR)
            | inr ratR' =>
                exact Or.inr (Or.inr ratR')
  · intro pairSupport
    have strict :
        RatHistoryCarrier l' ∨ RatHistoryCarrier l ∨ RatHistoryCarrier r ∨
          RatHistoryCarrier r' := by
      cases pairSupport with
      | inl leftPair =>
          cases leftPair with
          | inl ratL =>
              exact Or.inr (Or.inl ratL)
          | inr ratR =>
              exact Or.inr (Or.inr (Or.inl ratR))
      | inr rightPair =>
          cases rightPair with
          | inl ratL' =>
              exact Or.inl ratL'
          | inr ratR' =>
              exact Or.inr (Or.inr (Or.inr ratR'))
    exact Iff.mpr strictSupport strict

theorem RatDenomContextPair_product_commutative_support {l r l' r' : BHist} :
    RatDenomUnitCarrier l -> RatDenomUnitCarrier r -> RatDenomUnitCarrier l' ->
      RatDenomUnitCarrier r' ->
        RatDenomUnitClassifier (append l' l) (append l l') ∧
          RatDenomUnitClassifier (append r r') (append r' r) ∧
            (RatHistoryCarrier (append (append l' l) (append r r')) ↔
              (RatHistoryCarrier l ∨ RatHistoryCarrier r) ∨
                (RatHistoryCarrier l' ∨ RatHistoryCarrier r')) := by
  intro carrierL carrierR carrierL' carrierR'
  have leftClass : RatDenomUnitClassifier (append l' l) (append l l') :=
    RatDenomUnitClassifier_append_comm carrierL' carrierL
  have rightClass : RatDenomUnitClassifier (append r r') (append r' r) :=
    RatDenomUnitClassifier_append_comm carrierR carrierR'
  have strictSupport :=
    RatDenomContextPair_product_strict_support_iff carrierL carrierR carrierL' carrierR'
  constructor
  · exact leftClass
  constructor
  · exact rightClass
  constructor
  · intro productCarrier
    have support := Iff.mp strictSupport productCarrier
    cases support with
    | inl ratL' =>
        exact Or.inr (Or.inl ratL')
    | inr tailSupport =>
        cases tailSupport with
        | inl ratL =>
            exact Or.inl (Or.inl ratL)
        | inr rightSupport =>
            cases rightSupport with
            | inl ratR =>
                exact Or.inl (Or.inr ratR)
            | inr ratR' =>
                exact Or.inr (Or.inr ratR')
  · intro pairSupport
    have strict :
        RatHistoryCarrier l' ∨ RatHistoryCarrier l ∨ RatHistoryCarrier r ∨
          RatHistoryCarrier r' := by
      cases pairSupport with
      | inl leftPair =>
          cases leftPair with
          | inl ratL =>
              exact Or.inr (Or.inl ratL)
          | inr ratR =>
              exact Or.inr (Or.inr (Or.inl ratR))
      | inr rightPair =>
          cases rightPair with
          | inl ratL' =>
              exact Or.inl ratL'
          | inr ratR' =>
              exact Or.inr (Or.inr (Or.inr ratR'))
    exact Iff.mpr strictSupport strict

end BEDC.Derived.FieldUp
