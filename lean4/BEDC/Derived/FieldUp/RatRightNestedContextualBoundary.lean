import BEDC.Derived.FieldUp.RatDenomUnitAppendRat
import BEDC.Derived.FieldUp.RatBoundary

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem ratup_fieldup_right_nested_contextual_boundary {h k l y : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier l ->
      hsame y (append h (append k l)) ->
        ((RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l) ->
          (RatHistoryCarrier y ∧ (fieldSingletonEmptyCarrier y -> False)) ∧
            (∀ r : BHist,
              (fieldSingletonEmptyCarrier (append r y) -> False) ∧
              (fieldSingletonEmptyCarrier (append y r) -> False) ∧
              fieldSingletonEmptyNonZero (append r y) ∧
              fieldSingletonEmptyNonZero (append y r)) ∧
            (∀ L R : BHist,
              fieldSingletonEmptyClassifier (append L y) (append R y) -> False) := by
  intro carrierH carrierK carrierL sameY support
  have carrierKL : RatDenomUnitCarrier (append k l) :=
    RatDenomUnitCarrier_continuation_closed carrierK carrierL (cont_intro rfl)
  have productRat : RatHistoryCarrier (append h (append k l)) := by
    cases support with
    | inl leftSupport =>
        cases leftSupport with
        | inl ratH =>
            exact RatDenomUnitCarrier_append_left_rat_closed ratH carrierKL
        | inr ratK =>
            have ratKL : RatHistoryCarrier (append k l) :=
              RatDenomUnitCarrier_append_left_rat_closed ratK carrierL
            exact RatDenomUnitCarrier_append_right_rat_closed carrierH ratKL
    | inr ratL =>
        have ratKL : RatHistoryCarrier (append k l) :=
          RatDenomUnitCarrier_append_right_rat_closed carrierK ratL
        exact RatDenomUnitCarrier_append_right_rat_closed carrierH ratKL
  have carrierY : RatHistoryCarrier y :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameY) productRat
  have yNotSingleton : fieldSingletonEmptyCarrier y -> False := by
    intro singletonY
    exact RatHistoryCarrier_not_empty carrierY singletonY
  have classifierY : RatHistoryClassifier y y :=
    And.intro carrierY (And.intro carrierY (hsame_refl y))
  constructor
  · exact And.intro carrierY yNotSingleton
  · constructor
    · intro r
      have rightReject : fieldSingletonEmptyCarrier (append r y) -> False := by
        intro singleton
        exact fieldSingletonEmptyCarrier_append_ratHistoryCarrier_absurd singleton carrierY
      have leftReject : fieldSingletonEmptyCarrier (append y r) -> False := by
        intro singleton
        exact fieldSingletonEmptyCarrier_append_left_ratHistoryCarrier_absurd singleton carrierY
      constructor
      · exact rightReject
      · constructor
        · exact leftReject
        · constructor
          · intro classified
            exact rightReject classified.left
          · intro classified
            exact leftReject classified.left
    · intro L R singleton
      exact fieldSingletonEmptyClassifier_append_RatHistoryClassifier_absurd classifierY singleton

end BEDC.Derived.FieldUp
