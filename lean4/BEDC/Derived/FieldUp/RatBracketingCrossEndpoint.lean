import BEDC.Derived.FieldUp.RatDenomUnitAppendRat
import BEDC.Derived.FieldUp.RatBoundary

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem ratup_fieldup_bracketing_independent_cross_endpoint_classifier_boundary
    {h k l x y : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier l ->
      hsame x (append (append h k) l) -> hsame y (append h (append k l)) ->
        ((RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l) ->
          forall L R : BHist,
            (fieldSingletonEmptyClassifier (append L x) (append R y) -> False) ∧
              (fieldSingletonEmptyClassifier (append L y) (append R x) -> False) := by
  intro carrierH carrierK carrierL sameX sameY support L R
  have carrierHK : RatDenomUnitCarrier (append h k) :=
    RatDenomUnitCarrier_continuation_closed carrierH carrierK (cont_intro rfl)
  have ratLeft : RatHistoryCarrier (append (append h k) l) := by
    cases support with
    | inl leftSupport =>
        cases leftSupport with
        | inl ratH =>
            have ratHK : RatHistoryCarrier (append h k) :=
              RatDenomUnitCarrier_append_left_rat_closed ratH carrierK
            exact RatDenomUnitCarrier_append_left_rat_closed ratHK carrierL
        | inr ratK =>
            have ratHK : RatHistoryCarrier (append h k) :=
              RatDenomUnitCarrier_append_right_rat_closed carrierH ratK
            exact RatDenomUnitCarrier_append_left_rat_closed ratHK carrierL
    | inr ratL =>
        exact RatDenomUnitCarrier_append_right_rat_closed carrierHK ratL
  have ratRight : RatHistoryCarrier (append h (append k l)) :=
    RatHistoryCarrier_hsame_transport (append_assoc h k l) ratLeft
  have ratX : RatHistoryCarrier x :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameX) ratLeft
  have ratY : RatHistoryCarrier y :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameY) ratRight
  have sameXY : hsame x y :=
    hsame_trans sameX (hsame_trans (append_assoc h k l) (hsame_symm sameY))
  have classifierXY : RatHistoryClassifier x y :=
    And.intro ratX (And.intro ratY sameXY)
  have classifierYX : RatHistoryClassifier y x :=
    And.intro ratY (And.intro ratX (hsame_symm sameXY))
  constructor
  · intro singleton
    exact fieldSingletonEmptyClassifier_append_RatHistoryClassifier_absurd classifierXY singleton
  · intro singleton
    exact fieldSingletonEmptyClassifier_append_RatHistoryClassifier_absurd classifierYX singleton

end BEDC.Derived.FieldUp
