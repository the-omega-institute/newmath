import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

def RatDenomUnitContextualAction (p q l r h : BHist) : BHist :=
  append p (append (append (append l h) r) q)

theorem field_rat_denominator_contextual_action_unit_support_iff {h l r p q : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> RatDenomUnitCarrier h ->
      RatDenomUnitCarrier l -> RatDenomUnitCarrier r ->
        (RatHistoryCarrier l -> False) -> (RatHistoryCarrier r -> False) ->
          (RatHistoryCarrier (append p (append (append (append l h) r) q)) <->
            RatHistoryCarrier h) := by
  intro sameP sameQ carrierH carrierL carrierR notRatL notRatR
  have contextSame :
      hsame (append p (append (append (append l h) r) q)) (append (append l h) r) := by
    cases sameP
    cases sameQ
    exact hsame_trans
      (append_empty_left (append (append (append l h) r) BHist.Empty))
      (append_empty_right (append (append l h) r))
  have contextRat :
      RatHistoryCarrier (append p (append (append (append l h) r) q)) <->
        RatHistoryCarrier (append (append l h) r) := by
    constructor
    · intro ratContext
      exact RatHistoryCarrier_hsame_transport contextSame ratContext
    · intro ratCore
      exact RatHistoryCarrier_hsame_transport (hsame_symm contextSame) ratCore
  have supportRat :
      RatHistoryCarrier (append (append l h) r) <->
        RatHistoryCarrier l ∨ RatHistoryCarrier h ∨ RatHistoryCarrier r :=
    field_rat_denominator_empty_unit_bilateral_multiplication_support_exactness carrierH carrierL
      carrierR
  constructor
  · intro ratContext
    have ratCore : RatHistoryCarrier (append (append l h) r) := Iff.mp contextRat ratContext
    have support : RatHistoryCarrier l ∨ RatHistoryCarrier h ∨ RatHistoryCarrier r :=
      Iff.mp supportRat ratCore
    cases support with
    | inl ratL =>
        exact False.elim (notRatL ratL)
    | inr tailSupport =>
        cases tailSupport with
        | inl ratH =>
            exact ratH
        | inr ratR =>
            exact False.elim (notRatR ratR)
  · intro ratH
    have support : RatHistoryCarrier l ∨ RatHistoryCarrier h ∨ RatHistoryCarrier r :=
      Or.inr (Or.inl ratH)
    have ratCore : RatHistoryCarrier (append (append l h) r) := Iff.mpr supportRat support
    exact Iff.mpr contextRat ratCore

end BEDC.Derived.FieldUp
