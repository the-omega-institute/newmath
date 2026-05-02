import BEDC.Derived.FieldUp.RatBoundary
import BEDC.FKernel.Unary.Commutativity

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

def RatDenomUnitCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty ∨ RatHistoryCarrier h

def RatDenomUnitClassifier (h k : BHist) : Prop :=
  RatDenomUnitCarrier h ∧ RatDenomUnitCarrier k ∧ hsame h k

theorem RatDenomUnitCarrier_nonempty_rat {h : BHist} :
    RatDenomUnitCarrier h -> (hsame h BHist.Empty -> False) -> RatHistoryCarrier h := by
  intro carrier nonempty
  cases carrier with
  | inl emptyH =>
      exact False.elim (nonempty emptyH)
  | inr ratH =>
      exact ratH

theorem RatDenomUnitCarrier_hsame_transport {h k : BHist} :
    hsame h k -> RatDenomUnitCarrier h -> RatDenomUnitCarrier k := by
  intro sameHK carrierH
  cases carrierH with
  | inl emptyH =>
      left
      exact hsame_trans (hsame_symm sameHK) emptyH
  | inr ratH =>
      right
      exact RatHistoryCarrier_hsame_transport sameHK ratH

theorem RatDenomUnitCarrier_continuation_closed {h k r : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> Cont h k r ->
      RatDenomUnitCarrier r := by
  intro carrierH carrierK continuation
  cases carrierH with
  | inl emptyH =>
      cases carrierK with
      | inl emptyK =>
          left
          exact cont_respects_hsame emptyH emptyK continuation (cont_left_unit BHist.Empty)
      | inr ratK =>
          right
          have sameRK : hsame r k :=
            cont_respects_hsame emptyH (hsame_refl k) continuation (cont_left_unit k)
          exact RatHistoryCarrier_hsame_transport (hsame_symm sameRK) ratK
  | inr ratH =>
      cases carrierK with
      | inl emptyK =>
          right
          have sameRH : hsame r h :=
            cont_respects_hsame (hsame_refl h) emptyK continuation (cont_right_unit h)
          exact RatHistoryCarrier_hsame_transport (hsame_symm sameRH) ratH
      | inr ratK =>
          right
          exact field_rat_denominator_continuation_carrier_closure ratH ratK continuation

theorem RatDenomUnitCarrier_continuation_nonempty_rat_endpoint {h k r : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> Cont h k r ->
      (hsame r BHist.Empty -> False) -> RatHistoryCarrier h ∨ RatHistoryCarrier k := by
  intro carrierH carrierK hcont nonemptyR
  cases carrierH with
  | inl emptyH =>
      cases carrierK with
      | inl emptyK =>
          have resultEmpty : hsame r BHist.Empty :=
            cont_respects_hsame emptyH emptyK hcont (cont_left_unit BHist.Empty)
          exact False.elim (nonemptyR resultEmpty)
      | inr ratK =>
          exact Or.inr ratK
  | inr ratH =>
      exact Or.inl ratH

theorem field_rat_denominator_continuation_adjoined_unit_laws :
    RatDenomUnitCarrier BHist.Empty ∧
      (∀ {h k r : BHist}, RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> Cont h k r ->
        RatDenomUnitCarrier r) ∧
      (∀ {h r : BHist}, RatDenomUnitCarrier h -> Cont BHist.Empty h r ->
        RatDenomUnitClassifier r h) ∧
      (∀ {h r : BHist}, RatDenomUnitCarrier h -> Cont h BHist.Empty r ->
        RatDenomUnitClassifier r h) ∧
      (∀ {h k l hk kl left right : BHist}, RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
        RatDenomUnitCarrier l -> Cont h k hk -> Cont k l kl -> Cont hk l left ->
        Cont h kl right -> RatDenomUnitClassifier left right) := by
  constructor
  · left
    exact hsame_refl BHist.Empty
  · constructor
    · intro h k r carrierH carrierK continuation
      exact RatDenomUnitCarrier_continuation_closed carrierH carrierK continuation
    · constructor
      · intro h r carrierH continuation
        have carrierR : RatDenomUnitCarrier r :=
          RatDenomUnitCarrier_continuation_closed (Or.inl (hsame_refl BHist.Empty))
            carrierH continuation
        exact ⟨carrierR, carrierH, cont_left_unit_result continuation⟩
      · constructor
        · intro h r carrierH continuation
          have carrierR : RatDenomUnitCarrier r :=
            RatDenomUnitCarrier_continuation_closed carrierH
              (Or.inl (hsame_refl BHist.Empty)) continuation
          exact ⟨carrierR, carrierH, cont_right_unit_iff.mp continuation⟩
        · intro h k l hk kl left right carrierH carrierK carrierL contHK contKL
            contLeft contRight
          have carrierHK : RatDenomUnitCarrier hk :=
            RatDenomUnitCarrier_continuation_closed carrierH carrierK contHK
          have carrierKL : RatDenomUnitCarrier kl :=
            RatDenomUnitCarrier_continuation_closed carrierK carrierL contKL
          have carrierLeft : RatDenomUnitCarrier left :=
            RatDenomUnitCarrier_continuation_closed carrierHK carrierL contLeft
          have carrierRight : RatDenomUnitCarrier right :=
            RatDenomUnitCarrier_continuation_closed carrierH carrierKL contRight
          exact ⟨carrierLeft, carrierRight, cont_assoc_hsame contHK contLeft contKL contRight⟩

theorem field_rat_denominator_empty_unit_continuation_monoid_laws :
    RatDenomUnitCarrier BHist.Empty ∧
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
          RatDenomUnitClassifier (append h k) (append h' k')) := by
  constructor
  · exact field_rat_denominator_continuation_adjoined_unit_laws.left
  · constructor
    · intro h k carrierH carrierK
      exact RatDenomUnitCarrier_continuation_closed carrierH carrierK (cont_intro rfl)
    · constructor
      · intro h carrierH
        constructor
        · exact field_rat_denominator_continuation_adjoined_unit_laws.right.right.left
            carrierH (cont_intro rfl)
        · exact field_rat_denominator_continuation_adjoined_unit_laws.right.right.right.left
            carrierH (cont_intro rfl)
      · constructor
        · intro h k l carrierH carrierK carrierL
          exact field_rat_denominator_continuation_adjoined_unit_laws.right.right.right.right
            carrierH carrierK carrierL (cont_intro rfl) (cont_intro rfl) (cont_intro rfl)
            (cont_intro rfl)
        · intro h h' k k' classifiedH classifiedK
          have carrierHK : RatDenomUnitCarrier (append h k) :=
            RatDenomUnitCarrier_continuation_closed classifiedH.left classifiedK.left
              (cont_intro rfl)
          have carrierH'K' : RatDenomUnitCarrier (append h' k') :=
            RatDenomUnitCarrier_continuation_closed classifiedH.right.left classifiedK.right.left
              (cont_intro rfl)
          have sameAppend : hsame (append h k) (append h' k') :=
            cont_respects_hsame classifiedH.right.right classifiedK.right.right (cont_intro rfl)
              (cont_intro rfl)
          exact ⟨carrierHK, carrierH'K', sameAppend⟩

theorem field_rat_denominator_empty_unit_commutative_monoid_laws :
    RatDenomUnitCarrier BHist.Empty ∧
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
          RatDenomUnitClassifier (append h k) (append h' k')) ∧
      (∀ {h k : BHist}, RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
        RatDenomUnitClassifier (append h k) (append k h)) := by
  constructor
  · exact field_rat_denominator_empty_unit_continuation_monoid_laws.left
  · constructor
    · exact field_rat_denominator_empty_unit_continuation_monoid_laws.right.left
    · constructor
      · exact field_rat_denominator_empty_unit_continuation_monoid_laws.right.right.left
      · constructor
        · exact field_rat_denominator_empty_unit_continuation_monoid_laws.right.right.right.left
        · constructor
          · exact field_rat_denominator_empty_unit_continuation_monoid_laws.right.right.right.right
          · intro h k carrierH carrierK
            have carrierHK : RatDenomUnitCarrier (append h k) :=
              RatDenomUnitCarrier_continuation_closed carrierH carrierK (cont_intro rfl)
            have carrierKH : RatDenomUnitCarrier (append k h) :=
              RatDenomUnitCarrier_continuation_closed carrierK carrierH (cont_intro rfl)
            have sameHK : hsame (append h k) (append k h) := by
              cases carrierH with
              | inl emptyH =>
                  cases emptyH
                  cases carrierK with
                  | inl emptyK =>
                      cases emptyK
                      rfl
                  | inr ratK =>
                      exact (append_empty_left k).trans (append_empty_right k).symm
              | inr ratH =>
                  cases carrierK with
                  | inl emptyK =>
                      cases emptyK
                      exact (append_empty_right h).trans (append_empty_left h).symm
                  | inr ratK =>
                      have unaryH : UnaryHistory h :=
                        (PositiveUnaryDenominator_unary_and_nonempty
                          (RatHistoryCarrier_iff_positive_denominator.mp ratH)).left
                      have unaryK : UnaryHistory k :=
                        (PositiveUnaryDenominator_unary_and_nonempty
                          (RatHistoryCarrier_iff_positive_denominator.mp ratK)).left
                      exact unary_continuation_commutativity unaryH unaryK (cont_intro rfl)
                        (cont_intro rfl)
            exact ⟨carrierHK, carrierKH, sameHK⟩

theorem RatDenomUnitCarrier_e1_tail_unary_iff {tail : BHist} :
    RatDenomUnitCarrier (BHist.e1 tail) ↔ UnaryHistory tail := by
  constructor
  · intro carrier
    cases carrier with
    | inl emptyBranch =>
        exact False.elim (not_hsame_e1_empty emptyBranch)
    | inr ratBranch =>
        exact RatHistoryCarrier_e1_tail_unary_iff.mp ratBranch
  · intro tailUnary
    right
    exact RatHistoryCarrier_e1_tail_unary_iff.mpr tailUnary

theorem RatDenomUnitClassifier_mixed_endpoint_absurd {d e : BHist} :
    ((RatHistoryCarrier d ∧ hsame e BHist.Empty) ->
      (RatDenomUnitClassifier d e -> False)) ∧
    ((hsame d BHist.Empty ∧ RatHistoryCarrier e) ->
      (RatDenomUnitClassifier d e -> False)) := by
  constructor
  · intro endpointData classified
    have sameDE : hsame d e := classified.right.right
    exact RatHistoryCarrier_not_empty endpointData.left (hsame_trans sameDE endpointData.right)
  · intro endpointData classified
    have sameDE : hsame d e := classified.right.right
    exact RatHistoryCarrier_not_empty endpointData.right
      (hsame_trans (hsame_symm sameDE) endpointData.left)

theorem RatDenomUnitCarrier_empty_context_iff {p q h : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty ->
      (RatDenomUnitCarrier (append p (append h q)) ↔ RatDenomUnitCarrier h) := by
  intro sameP sameQ
  cases sameP
  cases sameQ
  constructor
  · intro carrier
    exact RatDenomUnitCarrier_hsame_transport (append_empty_left h) carrier
  · intro carrier
    exact RatDenomUnitCarrier_hsame_transport (hsame_symm (append_empty_left h)) carrier

end BEDC.Derived.FieldUp
