import BEDC.Derived.FieldUp.RatBoundary

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

def RatDenomUnitCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty ∨ RatHistoryCarrier h

def RatDenomUnitClassifier (h k : BHist) : Prop :=
  RatDenomUnitCarrier h ∧ RatDenomUnitCarrier k ∧ hsame h k

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

end BEDC.Derived.FieldUp
