import BEDC.Derived.FieldUp.ContextualAction

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatDenomUnitContextualAction_empty_unit_laws {h : BHist} :
    RatDenomUnitCarrier h ->
      RatDenomUnitCarrier
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty BHist.Empty BHist.Empty h) ∧
      RatDenomUnitClassifier
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty BHist.Empty BHist.Empty h) h ∧
      (RatHistoryCarrier
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty BHist.Empty BHist.Empty h) ↔
        RatHistoryCarrier h) := by
  intro carrierH
  have emptyCarrier : RatDenomUnitCarrier BHist.Empty :=
    field_rat_denominator_empty_unit_continuation_monoid_laws.left
  have sameAction :
      hsame
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty BHist.Empty BHist.Empty h) h := by
    unfold RatDenomUnitContextualAction
    exact hsame_trans (append_empty_left (append (append (append BHist.Empty h)
      BHist.Empty) BHist.Empty)) (hsame_trans (congrArg (fun x => append x BHist.Empty)
        (hsame_trans (append_empty_left (append h BHist.Empty)) (append_empty_right h)))
      (append_empty_right h))
  have carrierAction : RatDenomUnitCarrier
      (RatDenomUnitContextualAction BHist.Empty BHist.Empty BHist.Empty BHist.Empty h) :=
    RatDenomUnitCarrier_hsame_transport (hsame_symm sameAction) carrierH
  have notRatEmpty : RatHistoryCarrier BHist.Empty -> False :=
    fun ratEmpty => RatHistoryCarrier_not_empty ratEmpty (hsame_refl BHist.Empty)
  exact ⟨carrierAction, ⟨carrierAction, carrierH, sameAction⟩,
    field_rat_denominator_contextual_action_unit_support_iff
      (hsame_refl BHist.Empty) (hsame_refl BHist.Empty) carrierH emptyCarrier emptyCarrier
      notRatEmpty notRatEmpty⟩

theorem RatDenomUnitContextualAction_empty_unit_singleton_absurd {h : BHist} :
    RatDenomUnitCarrier h -> RatHistoryCarrier h ->
      fieldSingletonEmptyCarrier
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty BHist.Empty BHist.Empty h) ->
      False := by
  intro carrierH ratH singletonAction
  have laws := RatDenomUnitContextualAction_empty_unit_laws carrierH
  have ratAction : RatHistoryCarrier
      (RatDenomUnitContextualAction BHist.Empty BHist.Empty BHist.Empty BHist.Empty h) :=
    Iff.mpr laws.right.right ratH
  exact RatHistoryCarrier_not_empty ratAction singletonAction

end BEDC.Derived.FieldUp
