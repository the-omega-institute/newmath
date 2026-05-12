import BEDC.Derived.FieldUp.ContextualAction

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatDenomUnitContextualAction_contextual_action_certificate
    {h k l r p q p' q' : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
        RatDenomUnitCarrier l -> RatDenomUnitCarrier r ->
          (RatDenomUnitClassifier (RatDenomUnitContextualAction p q l r h)
              (RatDenomUnitContextualAction p' q' l r k) <->
            RatDenomUnitClassifier h k) ∧
          (RatHistoryCarrier (RatDenomUnitContextualAction p q l r h) <->
            RatHistoryCarrier l ∨ RatHistoryCarrier h ∨ RatHistoryCarrier r) ∧
          (RatHistoryCarrier (RatDenomUnitContextualAction p' q' l r k) <->
            RatHistoryCarrier l ∨ RatHistoryCarrier k ∨ RatHistoryCarrier r) := by
  intro sameP sameQ sameP' sameQ' carrierH carrierK carrierL carrierR
  have contextualClassifier :
      RatDenomUnitClassifier (RatDenomUnitContextualAction p q l r h)
          (RatDenomUnitContextualAction p' q' l r k) <->
        RatDenomUnitClassifier (append (append l h) r) (append (append l k) r) := by
    unfold RatDenomUnitContextualAction
    exact RatDenomUnitClassifier_empty_context_iff (p := p) (q := q) (p' := p')
      (q' := q') (h := append (append l h) r) (k := append (append l k) r)
      sameP sameQ sameP' sameQ'
  have bilateralClassifier :
      RatDenomUnitClassifier (append (append l h) r) (append (append l k) r) <->
        RatDenomUnitClassifier h k :=
    field_rat_denominator_empty_unit_bilateral_multiplication_classifier_exactness
      carrierH carrierK carrierL carrierR
  have classifierLaw :
      RatDenomUnitClassifier (RatDenomUnitContextualAction p q l r h)
          (RatDenomUnitContextualAction p' q' l r k) <->
        RatDenomUnitClassifier h k := by
    constructor
    · intro classified
      exact Iff.mp bilateralClassifier (Iff.mp contextualClassifier classified)
    · intro classified
      exact Iff.mpr contextualClassifier (Iff.mpr bilateralClassifier classified)
  have leftContextSame :
      hsame (RatDenomUnitContextualAction p q l r h) (append (append l h) r) := by
    unfold RatDenomUnitContextualAction
    cases sameP
    cases sameQ
    exact hsame_trans
      (append_empty_left (append (append (append l h) r) BHist.Empty))
      (append_empty_right (append (append l h) r))
  have rightContextSame :
      hsame (RatDenomUnitContextualAction p' q' l r k) (append (append l k) r) := by
    unfold RatDenomUnitContextualAction
    cases sameP'
    cases sameQ'
    exact hsame_trans
      (append_empty_left (append (append (append l k) r) BHist.Empty))
      (append_empty_right (append (append l k) r))
  have leftContextSupport :
      RatHistoryCarrier (RatDenomUnitContextualAction p q l r h) <->
        RatHistoryCarrier (append (append l h) r) := by
    constructor
    · intro ratAction
      exact RatHistoryCarrier_hsame_transport leftContextSame ratAction
    · intro ratCore
      exact RatHistoryCarrier_hsame_transport (hsame_symm leftContextSame) ratCore
  have rightContextSupport :
      RatHistoryCarrier (RatDenomUnitContextualAction p' q' l r k) <->
        RatHistoryCarrier (append (append l k) r) := by
    constructor
    · intro ratAction
      exact RatHistoryCarrier_hsame_transport rightContextSame ratAction
    · intro ratCore
      exact RatHistoryCarrier_hsame_transport (hsame_symm rightContextSame) ratCore
  have leftCoreSupport :
      RatHistoryCarrier (append (append l h) r) <->
        RatHistoryCarrier l ∨ RatHistoryCarrier h ∨ RatHistoryCarrier r :=
    field_rat_denominator_empty_unit_bilateral_multiplication_support_exactness
      carrierH carrierL carrierR
  have rightCoreSupport :
      RatHistoryCarrier (append (append l k) r) <->
        RatHistoryCarrier l ∨ RatHistoryCarrier k ∨ RatHistoryCarrier r :=
    field_rat_denominator_empty_unit_bilateral_multiplication_support_exactness
      carrierK carrierL carrierR
  have leftSupportLaw :
      RatHistoryCarrier (RatDenomUnitContextualAction p q l r h) <->
        RatHistoryCarrier l ∨ RatHistoryCarrier h ∨ RatHistoryCarrier r := by
    constructor
    · intro ratAction
      exact Iff.mp leftCoreSupport (Iff.mp leftContextSupport ratAction)
    · intro support
      exact Iff.mpr leftContextSupport (Iff.mpr leftCoreSupport support)
  have rightSupportLaw :
      RatHistoryCarrier (RatDenomUnitContextualAction p' q' l r k) <->
        RatHistoryCarrier l ∨ RatHistoryCarrier k ∨ RatHistoryCarrier r := by
    constructor
    · intro ratAction
      exact Iff.mp rightCoreSupport (Iff.mp rightContextSupport ratAction)
    · intro support
      exact Iff.mpr rightContextSupport (Iff.mpr rightCoreSupport support)
  exact ⟨classifierLaw, leftSupportLaw, rightSupportLaw⟩

theorem RatupFieldupDenominatorContextualAction_certificate {h k l r p q p' q' : BHist} :
    RatDenomUnitCarrier h ->
      RatDenomUnitCarrier k ->
        RatDenomUnitCarrier l ->
          RatDenomUnitCarrier r ->
            hsame p BHist.Empty ->
              hsame q BHist.Empty ->
                hsame p' BHist.Empty ->
                  hsame q' BHist.Empty ->
                    (RatDenomUnitClassifier (RatDenomUnitContextualAction p q l r h)
                        (RatDenomUnitContextualAction p' q' l r k) ↔
                      RatDenomUnitClassifier h k) := by
  intro carrierH carrierK carrierL carrierR sameP sameQ sameP' sameQ'
  exact
    (RatDenomUnitContextualAction_contextual_action_certificate
      (h := h) (k := k) (l := l) (r := r) (p := p) (q := q) (p' := p') (q' := q')
      sameP sameQ sameP' sameQ' carrierH carrierK carrierL carrierR).left

end BEDC.Derived.FieldUp
