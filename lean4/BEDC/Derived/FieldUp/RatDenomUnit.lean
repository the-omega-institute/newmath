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

theorem RatDenomUnitClassifier_e1_tail_iff {d e : BHist} :
    RatDenomUnitClassifier (BHist.e1 d) (BHist.e1 e) <->
      UnaryHistory d /\ UnaryHistory e /\ hsame d e := by
  constructor
  · intro classified
    have unaryD : UnaryHistory d :=
      RatDenomUnitCarrier_e1_tail_unary_iff.mp classified.left
    have unaryE : UnaryHistory e :=
      RatDenomUnitCarrier_e1_tail_unary_iff.mp classified.right.left
    have sameDE : hsame d e :=
      hsame_e1_iff.mp classified.right.right
    exact And.intro unaryD (And.intro unaryE sameDE)
  · intro tailData
    have carrierD : RatDenomUnitCarrier (BHist.e1 d) :=
      RatDenomUnitCarrier_e1_tail_unary_iff.mpr tailData.left
    have carrierE : RatDenomUnitCarrier (BHist.e1 e) :=
      RatDenomUnitCarrier_e1_tail_unary_iff.mpr tailData.right.left
    have sameDE : hsame (BHist.e1 d) (BHist.e1 e) :=
      hsame_e1_iff.mpr tailData.right.right
    exact And.intro carrierD (And.intro carrierE sameDE)

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

theorem field_rat_denominator_empty_unit_product_nonempty_iff {h k : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
      ((hsame (append h k) BHist.Empty -> False) ↔
        RatHistoryCarrier h ∨ RatHistoryCarrier k) := by
  intro carrierH carrierK
  constructor
  · intro nonemptyProduct
    exact
      RatDenomUnitCarrier_continuation_nonempty_rat_endpoint carrierH carrierK (cont_intro rfl)
        nonemptyProduct
  · intro strictSupport productEmpty
    cases strictSupport with
    | inl ratH =>
        cases carrierK with
        | inl emptyK =>
            have sameProductH : hsame (append h k) h :=
              cont_respects_hsame (hsame_refl h) emptyK (cont_intro rfl) (cont_right_unit h)
            exact RatHistoryCarrier_not_empty ratH
              (hsame_trans (hsame_symm sameProductH) productEmpty)
        | inr ratK =>
            have productCarrier : RatHistoryCarrier (append h k) :=
              field_rat_denominator_continuation_carrier_closure ratH ratK (cont_intro rfl)
            exact RatHistoryCarrier_not_empty productCarrier productEmpty
    | inr ratK =>
        cases carrierH with
        | inl emptyH =>
            have sameProductK : hsame (append h k) k :=
              cont_respects_hsame emptyH (hsame_refl k) (cont_intro rfl) (cont_left_unit k)
            exact RatHistoryCarrier_not_empty ratK
              (hsame_trans (hsame_symm sameProductK) productEmpty)
        | inr ratH =>
            have productCarrier : RatHistoryCarrier (append h k) :=
              field_rat_denominator_continuation_carrier_closure ratH ratK (cont_intro rfl)
            exact RatHistoryCarrier_not_empty productCarrier productEmpty

theorem field_rat_denominator_empty_unit_strict_product_factor_cases {h k : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatHistoryCarrier (append h k) ->
      (RatHistoryCarrier h ∧ RatDenomUnitCarrier k) ∨
        (RatDenomUnitCarrier h ∧ RatHistoryCarrier k) := by
  intro carrierH carrierK productCarrier
  have productNonempty : hsame (append h k) BHist.Empty -> False :=
    RatHistoryCarrier_not_empty productCarrier
  have strictSupport : RatHistoryCarrier h ∨ RatHistoryCarrier k :=
    Iff.mp (field_rat_denominator_empty_unit_product_nonempty_iff carrierH carrierK)
      productNonempty
  cases strictSupport with
  | inl ratH => exact Or.inl (And.intro ratH carrierK)
  | inr ratK => exact Or.inr (And.intro carrierH ratK)

theorem field_rat_denominator_empty_unit_bilateral_multiplication_support_exactness
    {h l r : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier l -> RatDenomUnitCarrier r ->
      (RatHistoryCarrier (append (append l h) r) <->
        RatHistoryCarrier l ∨ RatHistoryCarrier h ∨ RatHistoryCarrier r) := by
  intro carrierH carrierL carrierR
  have carrierLH : RatDenomUnitCarrier (append l h) :=
    RatDenomUnitCarrier_continuation_closed carrierL carrierH (cont_intro rfl)
  have carrierLHR : RatDenomUnitCarrier (append (append l h) r) :=
    RatDenomUnitCarrier_continuation_closed carrierLH carrierR (cont_intro rfl)
  have innerSupport :=
    field_rat_denominator_empty_unit_product_nonempty_iff carrierL carrierH
  have outerSupport :=
    field_rat_denominator_empty_unit_product_nonempty_iff carrierLH carrierR
  constructor
  · intro productCarrier
    have productNonempty : hsame (append (append l h) r) BHist.Empty -> False :=
      RatHistoryCarrier_not_empty productCarrier
    have outerStrict : RatHistoryCarrier (append l h) ∨ RatHistoryCarrier r :=
      Iff.mp outerSupport productNonempty
    cases outerStrict with
    | inl leftProductCarrier =>
        have leftProductNonempty : hsame (append l h) BHist.Empty -> False :=
          RatHistoryCarrier_not_empty leftProductCarrier
        have innerStrict : RatHistoryCarrier l ∨ RatHistoryCarrier h :=
          Iff.mp innerSupport leftProductNonempty
        cases innerStrict with
        | inl ratL =>
            exact Or.inl ratL
        | inr ratH =>
            exact Or.inr (Or.inl ratH)
    | inr ratR =>
        exact Or.inr (Or.inr ratR)
  · intro strictSupport
    have leftProductCarrier : RatHistoryCarrier (append l h) ∨ RatHistoryCarrier r := by
      cases strictSupport with
      | inl ratL =>
          have leftProductNonempty : hsame (append l h) BHist.Empty -> False :=
            Iff.mpr innerSupport (Or.inl ratL)
          exact Or.inl
            (RatDenomUnitCarrier_nonempty_rat carrierLH leftProductNonempty)
      | inr tailSupport =>
          cases tailSupport with
          | inl ratH =>
              have leftProductNonempty : hsame (append l h) BHist.Empty -> False :=
                Iff.mpr innerSupport (Or.inr ratH)
              exact Or.inl
                (RatDenomUnitCarrier_nonempty_rat carrierLH leftProductNonempty)
          | inr ratR =>
              exact Or.inr ratR
    have productNonempty : hsame (append (append l h) r) BHist.Empty -> False :=
      Iff.mpr outerSupport leftProductCarrier
    exact RatDenomUnitCarrier_nonempty_rat carrierLHR productNonempty

theorem field_rat_denominator_empty_unit_contextual_strict_product_support_exactness
    {p q h k : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> RatDenomUnitCarrier h ->
      RatDenomUnitCarrier k ->
        (RatHistoryCarrier (append p (append (append h k) q)) <->
          RatHistoryCarrier h ∨ RatHistoryCarrier k) := by
  intro sameP sameQ carrierH carrierK
  have contextSame : hsame (append p (append (append h k) q)) (append h k) := by
    cases sameP
    cases sameQ
    exact hsame_trans (append_empty_left (append (append h k) BHist.Empty))
      (append_empty_right (append h k))
  have productCarrier : RatDenomUnitCarrier (append h k) :=
    RatDenomUnitCarrier_continuation_closed carrierH carrierK (cont_intro rfl)
  have productSupport :=
    field_rat_denominator_empty_unit_product_nonempty_iff carrierH carrierK
  constructor
  · intro contextualCarrier
    have productRat : RatHistoryCarrier (append h k) :=
      RatHistoryCarrier_hsame_transport contextSame contextualCarrier
    exact Iff.mp productSupport (RatHistoryCarrier_not_empty productRat)
  · intro strictSupport
    have productNonempty : hsame (append h k) BHist.Empty -> False :=
      Iff.mpr productSupport strictSupport
    have productRat : RatHistoryCarrier (append h k) :=
      RatDenomUnitCarrier_nonempty_rat productCarrier productNonempty
    exact RatHistoryCarrier_hsame_transport (hsame_symm contextSame) productRat

theorem RatDenomUnitClassifier_empty_context_iff {p q p' q' h k : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty ->
        (RatDenomUnitClassifier (append p (append h q)) (append p' (append k q')) ↔
          RatDenomUnitClassifier h k) := by
  intro sameP sameQ sameP' sameQ'
  have leftCarrierIff := RatDenomUnitCarrier_empty_context_iff (p := p) (q := q)
    (h := h) sameP sameQ
  have rightCarrierIff := RatDenomUnitCarrier_empty_context_iff (p := p') (q := q')
    (h := k) sameP' sameQ'
  have leftSame : hsame (append p (append h q)) h := by
    cases sameP
    cases sameQ
    exact hsame_trans (append_empty_left (append h BHist.Empty)) (append_empty_right h)
  have rightSame : hsame (append p' (append k q')) k := by
    cases sameP'
    cases sameQ'
    exact hsame_trans (append_empty_left (append k BHist.Empty)) (append_empty_right k)
  constructor
  · intro classified
    have carrierH : RatDenomUnitCarrier h := Iff.mp leftCarrierIff classified.left
    have carrierK : RatDenomUnitCarrier k := Iff.mp rightCarrierIff classified.right.left
    have sameHK : hsame h k :=
      hsame_trans (hsame_symm leftSame)
        (hsame_trans classified.right.right rightSame)
    exact ⟨carrierH, carrierK, sameHK⟩
  · intro classified
    have carrierLeft : RatDenomUnitCarrier (append p (append h q)) :=
      Iff.mpr leftCarrierIff classified.left
    have carrierRight : RatDenomUnitCarrier (append p' (append k q')) :=
      Iff.mpr rightCarrierIff classified.right.left
    have sameContext : hsame (append p (append h q)) (append p' (append k q')) :=
      hsame_trans leftSame
        (hsame_trans classified.right.right (hsame_symm rightSame))
    exact ⟨carrierLeft, carrierRight, sameContext⟩

theorem field_rat_denominator_empty_unit_contextual_commutativity {p q p' q' h k : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
        RatDenomUnitClassifier (append p (append (append h k) q))
          (append p' (append (append k h) q')) := by
  intro sameP sameQ sameP' sameQ' carrierH carrierK
  have core : RatDenomUnitClassifier (append h k) (append k h) :=
    field_rat_denominator_empty_unit_commutative_monoid_laws.right.right.right.right.right
      carrierH carrierK
  exact (RatDenomUnitClassifier_empty_context_iff sameP sameQ sameP' sameQ').mpr core

theorem field_rat_denominator_empty_unit_identity_unique {u : BHist} :
    RatDenomUnitCarrier u ->
      (forall {h : BHist}, RatDenomUnitCarrier h ->
        RatDenomUnitClassifier (append u h) h) ->
      (forall {h : BHist}, RatDenomUnitCarrier h ->
        RatDenomUnitClassifier (append h u) h) ->
        RatDenomUnitClassifier u BHist.Empty := by
  intro carrierU leftUnit _rightUnit
  have carrierEmpty : RatDenomUnitCarrier BHist.Empty :=
    field_rat_denominator_empty_unit_continuation_monoid_laws.left
  have leftAtEmpty : RatDenomUnitClassifier (append u BHist.Empty) BHist.Empty :=
    leftUnit carrierEmpty
  have sameUEmpty : hsame u BHist.Empty :=
    hsame_trans (hsame_symm (append_empty_right u)) leftAtEmpty.right.right
  exact ⟨carrierU, carrierEmpty, sameUEmpty⟩

theorem field_rat_denominator_empty_unit_right_cancel {h k t : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier t ->
      RatDenomUnitClassifier (append h t) (append k t) -> RatDenomUnitClassifier h k := by
  intro carrierH carrierK _carrierT classified
  exact ⟨carrierH, carrierK, append_right_cancel classified.right.right⟩

theorem field_rat_denominator_empty_unit_right_multiplication_classifier_exactness
    {h k t : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier t ->
      (RatDenomUnitClassifier (append h t) (append k t) ↔ RatDenomUnitClassifier h k) := by
  intro carrierH carrierK carrierT
  constructor
  · intro classified
    exact field_rat_denominator_empty_unit_right_cancel carrierH carrierK carrierT classified
  · intro classified
    have carrierHT : RatDenomUnitCarrier (append h t) :=
      RatDenomUnitCarrier_continuation_closed carrierH carrierT (cont_intro rfl)
    have carrierKT : RatDenomUnitCarrier (append k t) :=
      RatDenomUnitCarrier_continuation_closed carrierK carrierT (cont_intro rfl)
    exact ⟨carrierHT, carrierKT, congrArg (fun x => append x t) classified.right.right⟩

theorem field_rat_denominator_empty_unit_left_multiplication_classifier_exactness
    {h k t : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier t ->
      (RatDenomUnitClassifier (append t h) (append t k) <->
        RatDenomUnitClassifier h k) := by
  intro carrierH carrierK carrierT
  constructor
  · intro classified
    exact ⟨carrierH, carrierK, append_left_cancel classified.right.right⟩
  · intro classified
    have carrierTH : RatDenomUnitCarrier (append t h) :=
      RatDenomUnitCarrier_continuation_closed carrierT carrierH (cont_intro rfl)
    have carrierTK : RatDenomUnitCarrier (append t k) :=
      RatDenomUnitCarrier_continuation_closed carrierT carrierK (cont_intro rfl)
    exact ⟨carrierTH, carrierTK, congrArg (append t) classified.right.right⟩

theorem field_rat_denominator_empty_unit_bilateral_multiplication_classifier_exactness
    {h k l r : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier l ->
      RatDenomUnitCarrier r ->
        (RatDenomUnitClassifier (append (append l h) r) (append (append l k) r) <->
          RatDenomUnitClassifier h k) := by
  intro carrierH carrierK carrierL carrierR
  have carrierLH : RatDenomUnitCarrier (append l h) :=
    RatDenomUnitCarrier_continuation_closed carrierL carrierH (cont_intro rfl)
  have carrierLK : RatDenomUnitCarrier (append l k) :=
    RatDenomUnitCarrier_continuation_closed carrierL carrierK (cont_intro rfl)
  constructor
  · intro classified
    have leftClassified : RatDenomUnitClassifier (append l h) (append l k) :=
      field_rat_denominator_empty_unit_right_cancel carrierLH carrierLK carrierR classified
    exact
      (field_rat_denominator_empty_unit_left_multiplication_classifier_exactness
        carrierH carrierK carrierL).mp leftClassified
  · intro classified
    have leftClassified : RatDenomUnitClassifier (append l h) (append l k) :=
      (field_rat_denominator_empty_unit_left_multiplication_classifier_exactness
        carrierH carrierK carrierL).mpr classified
    have carrierLHR : RatDenomUnitCarrier (append (append l h) r) :=
      RatDenomUnitCarrier_continuation_closed carrierLH carrierR (cont_intro rfl)
    have carrierLKR : RatDenomUnitCarrier (append (append l k) r) :=
      RatDenomUnitCarrier_continuation_closed carrierLK carrierR (cont_intro rfl)
    exact ⟨carrierLHR, carrierLKR, congrArg (fun x => append x r) leftClassified.right.right⟩

theorem field_rat_denominator_empty_unit_contextual_multiplication_classifier_exactness
    {p q p' q' h k t : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
        RatDenomUnitCarrier t ->
          ((RatDenomUnitClassifier (append p (append (append h t) q))
              (append p' (append (append k t) q')) <->
            RatDenomUnitClassifier h k) /\
          (RatDenomUnitClassifier (append p (append (append t h) q))
              (append p' (append (append t k) q')) <->
            RatDenomUnitClassifier h k)) := by
  intro sameP sameQ sameP' sameQ' carrierH carrierK carrierT
  have rightContextIff :
      RatDenomUnitClassifier (append p (append (append h t) q))
          (append p' (append (append k t) q')) <->
        RatDenomUnitClassifier (append h t) (append k t) :=
    RatDenomUnitClassifier_empty_context_iff (p := p) (q := q) (p' := p') (q' := q')
      (h := append h t) (k := append k t) sameP sameQ sameP' sameQ'
  have rightActionIff :
      RatDenomUnitClassifier (append h t) (append k t) <->
        RatDenomUnitClassifier h k := by
    constructor
    · intro classified
      exact field_rat_denominator_empty_unit_right_cancel carrierH carrierK carrierT classified
    · intro classified
      have carrierHT : RatDenomUnitCarrier (append h t) :=
        RatDenomUnitCarrier_continuation_closed carrierH carrierT (cont_intro rfl)
      have carrierKT : RatDenomUnitCarrier (append k t) :=
        RatDenomUnitCarrier_continuation_closed carrierK carrierT (cont_intro rfl)
      exact ⟨carrierHT, carrierKT, congrArg (fun x => append x t) classified.right.right⟩
  have leftContextIff :
      RatDenomUnitClassifier (append p (append (append t h) q))
          (append p' (append (append t k) q')) <->
        RatDenomUnitClassifier (append t h) (append t k) :=
    RatDenomUnitClassifier_empty_context_iff (p := p) (q := q) (p' := p') (q' := q')
      (h := append t h) (k := append t k) sameP sameQ sameP' sameQ'
  have leftActionIff :
      RatDenomUnitClassifier (append t h) (append t k) <->
        RatDenomUnitClassifier h k :=
    field_rat_denominator_empty_unit_left_multiplication_classifier_exactness carrierH carrierK
      carrierT
  constructor
  · constructor
    · intro classified
      exact Iff.mp rightActionIff (Iff.mp rightContextIff classified)
    · intro classified
      exact Iff.mpr rightContextIff (Iff.mpr rightActionIff classified)
  · constructor
    · intro classified
      exact Iff.mp leftActionIff (Iff.mp leftContextIff classified)
    · intro classified
      exact Iff.mpr leftContextIff (Iff.mpr leftActionIff classified)

theorem field_rat_denominator_empty_unit_context_action_support_exactness
    {p q p' q' h k t : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
        RatDenomUnitCarrier t ->
          (RatDenomUnitClassifier (append h t) (append k t) <->
            RatDenomUnitClassifier h k) /\
          (RatDenomUnitClassifier (append t h) (append t k) <->
            RatDenomUnitClassifier h k) /\
          (RatDenomUnitClassifier (append p (append h q)) (append p' (append k q')) <->
            RatDenomUnitClassifier h k) /\
          (RatHistoryCarrier (append p (append h q)) <-> RatHistoryCarrier h) /\
          (RatHistoryCarrier (append p' (append k q')) <-> RatHistoryCarrier k) /\
          (RatHistoryCarrier (append h t) <-> RatHistoryCarrier h \/ RatHistoryCarrier t) /\
          (RatHistoryCarrier (append t h) <-> RatHistoryCarrier t \/ RatHistoryCarrier h) := by
  intro sameP sameQ sameP' sameQ' carrierH carrierK carrierT
  have rightActionIff :
      RatDenomUnitClassifier (append h t) (append k t) <->
        RatDenomUnitClassifier h k := by
    constructor
    · intro classified
      exact field_rat_denominator_empty_unit_right_cancel carrierH carrierK carrierT classified
    · intro classified
      have carrierHT : RatDenomUnitCarrier (append h t) :=
        RatDenomUnitCarrier_continuation_closed carrierH carrierT (cont_intro rfl)
      have carrierKT : RatDenomUnitCarrier (append k t) :=
        RatDenomUnitCarrier_continuation_closed carrierK carrierT (cont_intro rfl)
      exact ⟨carrierHT, carrierKT, congrArg (fun x => append x t) classified.right.right⟩
  have leftActionIff :
      RatDenomUnitClassifier (append t h) (append t k) <->
        RatDenomUnitClassifier h k :=
    field_rat_denominator_empty_unit_left_multiplication_classifier_exactness carrierH carrierK
      carrierT
  have contextIff :
      RatDenomUnitClassifier (append p (append h q)) (append p' (append k q')) <->
        RatDenomUnitClassifier h k :=
    RatDenomUnitClassifier_empty_context_iff (p := p) (q := q) (p' := p') (q' := q')
      (h := h) (k := k) sameP sameQ sameP' sameQ'
  have contextSameH : hsame (append p (append h q)) h := by
    cases sameP
    cases sameQ
    exact hsame_trans (append_empty_left (append h BHist.Empty)) (append_empty_right h)
  have contextSameK : hsame (append p' (append k q')) k := by
    cases sameP'
    cases sameQ'
    exact hsame_trans (append_empty_left (append k BHist.Empty)) (append_empty_right k)
  have contextRatH : RatHistoryCarrier (append p (append h q)) <-> RatHistoryCarrier h := by
    constructor
    · intro ratContext
      exact RatHistoryCarrier_hsame_transport contextSameH ratContext
    · intro ratH
      exact RatHistoryCarrier_hsame_transport (hsame_symm contextSameH) ratH
  have contextRatK : RatHistoryCarrier (append p' (append k q')) <-> RatHistoryCarrier k := by
    constructor
    · intro ratContext
      exact RatHistoryCarrier_hsame_transport contextSameK ratContext
    · intro ratK
      exact RatHistoryCarrier_hsame_transport (hsame_symm contextSameK) ratK
  have carrierHT : RatDenomUnitCarrier (append h t) :=
    RatDenomUnitCarrier_continuation_closed carrierH carrierT (cont_intro rfl)
  have carrierTH : RatDenomUnitCarrier (append t h) :=
    RatDenomUnitCarrier_continuation_closed carrierT carrierH (cont_intro rfl)
  have productRightSupport :
      RatHistoryCarrier (append h t) <-> RatHistoryCarrier h \/ RatHistoryCarrier t := by
    have nonemptyIff :=
      field_rat_denominator_empty_unit_product_nonempty_iff carrierH carrierT
    constructor
    · intro ratProduct
      exact Iff.mp nonemptyIff (fun emptyProduct =>
        RatHistoryCarrier_not_empty ratProduct emptyProduct)
    · intro factorSupport
      have nonemptyProduct : hsame (append h t) BHist.Empty -> False :=
        Iff.mpr nonemptyIff factorSupport
      exact RatDenomUnitCarrier_nonempty_rat carrierHT nonemptyProduct
  have productLeftSupport :
      RatHistoryCarrier (append t h) <-> RatHistoryCarrier t \/ RatHistoryCarrier h := by
    have nonemptyIff :=
      field_rat_denominator_empty_unit_product_nonempty_iff carrierT carrierH
    constructor
    · intro ratProduct
      exact Iff.mp nonemptyIff (fun emptyProduct =>
        RatHistoryCarrier_not_empty ratProduct emptyProduct)
    · intro factorSupport
      have nonemptyProduct : hsame (append t h) BHist.Empty -> False :=
        Iff.mpr nonemptyIff factorSupport
      exact RatDenomUnitCarrier_nonempty_rat carrierTH nonemptyProduct
  constructor
  · exact rightActionIff
  · constructor
    · exact leftActionIff
    · constructor
      · exact contextIff
      · constructor
        · exact contextRatH
        · constructor
          · exact contextRatK
          · constructor
            · exact productRightSupport
            · exact productLeftSupport

end BEDC.Derived.FieldUp
