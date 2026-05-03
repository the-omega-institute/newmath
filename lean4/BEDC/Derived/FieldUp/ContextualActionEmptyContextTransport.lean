import BEDC.Derived.FieldUp.ContextualAction

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatDenomUnitContextualAction_empty_context_hsame_transport {h h' l r : BHist} :
    RatDenomUnitCarrier l -> RatDenomUnitCarrier r -> RatDenomUnitClassifier h h' ->
      RatDenomUnitClassifier
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l r h)
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l r h') := by
  intro carrierL carrierR classifiedH
  have classifiedL : RatDenomUnitClassifier l l :=
    ⟨carrierL, carrierL, hsame_refl l⟩
  have classifiedR : RatDenomUnitClassifier r r :=
    ⟨carrierR, carrierR, hsame_refl r⟩
  have classifiedLH : RatDenomUnitClassifier (append l h) (append l h') :=
    RatDenomUnitClassifier_continuation_closed classifiedL classifiedH
      (cont_intro rfl) (cont_intro rfl)
  have core :
      RatDenomUnitClassifier (append (append l h) r) (append (append l h') r) :=
    RatDenomUnitClassifier_continuation_closed classifiedLH classifiedR
      (cont_intro rfl) (cont_intro rfl)
  unfold RatDenomUnitContextualAction
  exact
    (RatDenomUnitClassifier_empty_context_iff (hsame_refl BHist.Empty)
      (hsame_refl BHist.Empty) (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)).mpr
      core

end BEDC.Derived.FieldUp
