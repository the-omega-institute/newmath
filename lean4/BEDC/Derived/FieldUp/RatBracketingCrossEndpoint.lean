import BEDC.Derived.FieldUp.RatDenomUnitAppendRat
import BEDC.Derived.FieldUp.RatBoundary

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

def ratup_fieldup_bracketing_endpoint_selector (h k l : BHist)
    (s : BEDC.FKernel.Mark.BMark) : BHist :=
  match s with
  | BEDC.FKernel.Mark.BMark.b0 => append (append h k) l
  | BEDC.FKernel.Mark.BMark.b1 => append h (append k l)

theorem ratup_fieldup_bracketing_selector_rat_carrier_coverage {h k l : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier l ->
      ((RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l) ->
        forall s : BEDC.FKernel.Mark.BMark,
          RatHistoryCarrier (ratup_fieldup_bracketing_endpoint_selector h k l s) := by
  intro carrierH carrierK carrierL support s
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
  cases s with
  | b0 => exact ratLeft
  | b1 => exact ratRight

theorem ratup_fieldup_bracketing_selector_denominator_classifier_coverage {h k l : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier l ->
      ((RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l) ->
        forall s t : BEDC.FKernel.Mark.BMark,
          RatHistoryClassifier (ratup_fieldup_bracketing_endpoint_selector h k l s)
            (ratup_fieldup_bracketing_endpoint_selector h k l t) := by
  intro carrierH carrierK carrierL support s t
  have selectedCarrier :
      forall u : BEDC.FKernel.Mark.BMark,
        RatHistoryCarrier (ratup_fieldup_bracketing_endpoint_selector h k l u) :=
    ratup_fieldup_bracketing_selector_rat_carrier_coverage
      carrierH carrierK carrierL support
  have selectedSame :
      forall u v : BEDC.FKernel.Mark.BMark,
        hsame (ratup_fieldup_bracketing_endpoint_selector h k l u)
          (ratup_fieldup_bracketing_endpoint_selector h k l v) := by
    intro u v
    cases u with
    | b0 =>
        cases v with
        | b0 => exact hsame_refl (append (append h k) l)
        | b1 => exact append_assoc h k l
    | b1 =>
        cases v with
        | b0 => exact hsame_symm (append_assoc h k l)
        | b1 => exact hsame_refl (append h (append k l))
  exact And.intro (selectedCarrier s) (And.intro (selectedCarrier t) (selectedSame s t))

theorem ratup_fieldup_bracketing_selector_rat_classifier_coverage {h k l : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier l ->
      ((RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l) ->
        forall s t : BEDC.FKernel.Mark.BMark,
          RatHistoryClassifier (ratup_fieldup_bracketing_endpoint_selector h k l s)
            (ratup_fieldup_bracketing_endpoint_selector h k l t) := by
  intro carrierH carrierK carrierL support s t
  have selectedCarrier :
      forall u : BEDC.FKernel.Mark.BMark,
        RatHistoryCarrier (ratup_fieldup_bracketing_endpoint_selector h k l u) :=
    ratup_fieldup_bracketing_selector_rat_carrier_coverage
      carrierH carrierK carrierL support
  have selectedSame :
      hsame (ratup_fieldup_bracketing_endpoint_selector h k l s)
        (ratup_fieldup_bracketing_endpoint_selector h k l t) := by
    cases s with
    | b0 =>
        cases t with
        | b0 => exact hsame_refl (append (append h k) l)
        | b1 => exact append_assoc h k l
    | b1 =>
        cases t with
        | b0 => exact hsame_symm (append_assoc h k l)
        | b1 => exact hsame_refl (append h (append k l))
  exact And.intro (selectedCarrier s) (And.intro (selectedCarrier t) selectedSame)

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

theorem ratup_fieldup_bracketing_selector_classifier_exclusion {h k l : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier l ->
      ((RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l) ->
        forall s t : BEDC.FKernel.Mark.BMark, forall L R : BHist,
          fieldSingletonEmptyClassifier
            (append L (ratup_fieldup_bracketing_endpoint_selector h k l s))
            (append R (ratup_fieldup_bracketing_endpoint_selector h k l t)) -> False := by
  intro carrierH carrierK carrierL support s t L R singleton
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
  have selectedCarrier :
      forall u : BEDC.FKernel.Mark.BMark,
        RatHistoryCarrier (ratup_fieldup_bracketing_endpoint_selector h k l u) := by
    intro u
    cases u with
    | b0 => exact ratLeft
    | b1 => exact ratRight
  have selectedSame :
      forall u v : BEDC.FKernel.Mark.BMark,
        hsame (ratup_fieldup_bracketing_endpoint_selector h k l u)
          (ratup_fieldup_bracketing_endpoint_selector h k l v) := by
    intro u v
    cases u with
    | b0 =>
        cases v with
        | b0 => exact hsame_refl (append (append h k) l)
        | b1 => exact append_assoc h k l
    | b1 =>
        cases v with
        | b0 => exact hsame_symm (append_assoc h k l)
        | b1 => exact hsame_refl (append h (append k l))
  have classified :
      RatHistoryClassifier (ratup_fieldup_bracketing_endpoint_selector h k l s)
        (ratup_fieldup_bracketing_endpoint_selector h k l t) :=
    And.intro (selectedCarrier s) (And.intro (selectedCarrier t) (selectedSame s t))
  exact fieldSingletonEmptyClassifier_append_RatHistoryClassifier_absurd classified singleton

theorem ratup_fieldup_bracketing_endpoint_selector_carrier_coverage {h k l : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier l ->
      ((RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l) ->
        RatHistoryCarrier (append (append h k) l) ∧
          RatHistoryCarrier (append h (append k l)) ∧
            (forall s : BEDC.FKernel.Mark.BMark,
              RatHistoryCarrier (ratup_fieldup_bracketing_endpoint_selector h k l s)) := by
  intro carrierH carrierK carrierL support
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
  constructor
  · exact ratLeft
  · constructor
    · exact ratRight
    · intro s
      cases s with
      | b0 => exact ratLeft
      | b1 => exact ratRight

theorem ratup_fieldup_bracketing_endpoint_selector_same {h k l : BHist} :
    (forall s : BEDC.FKernel.Mark.BMark,
      hsame (ratup_fieldup_bracketing_endpoint_selector h k l s) (append (append h k) l) ∨
        hsame (ratup_fieldup_bracketing_endpoint_selector h k l s) (append h (append k l))) ∧
      (forall s t : BEDC.FKernel.Mark.BMark,
        hsame (ratup_fieldup_bracketing_endpoint_selector h k l s)
          (ratup_fieldup_bracketing_endpoint_selector h k l t)) := by
  constructor
  · intro s
    cases s with
    | b0 => exact Or.inl (hsame_refl (append (append h k) l))
    | b1 => exact Or.inr (hsame_refl (append h (append k l)))
  · intro s t
    cases s with
    | b0 =>
        cases t with
        | b0 => exact hsame_refl (append (append h k) l)
        | b1 => exact append_assoc h k l
    | b1 =>
        cases t with
        | b0 => exact hsame_symm (append_assoc h k l)
        | b1 => exact hsame_refl (append h (append k l))

theorem ratup_fieldup_bracketing_selector_contextual_nonzero_package {h k l ctx : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier l ->
      ((RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l) ->
        forall s : BEDC.FKernel.Mark.BMark,
          (fieldSingletonEmptyCarrier
            (append ctx (ratup_fieldup_bracketing_endpoint_selector h k l s)) -> False) ∧
            (fieldSingletonEmptyCarrier
              (append (ratup_fieldup_bracketing_endpoint_selector h k l s) ctx) -> False) ∧
            fieldSingletonEmptyNonZero
              (append ctx (ratup_fieldup_bracketing_endpoint_selector h k l s)) ∧
            fieldSingletonEmptyNonZero
              (append (ratup_fieldup_bracketing_endpoint_selector h k l s) ctx) := by
  intro carrierH carrierK carrierL support s
  have selectedCarrier :
      RatHistoryCarrier (ratup_fieldup_bracketing_endpoint_selector h k l s) :=
    ratup_fieldup_bracketing_selector_rat_carrier_coverage
      carrierH carrierK carrierL support s
  have rightContextEmpty :
      fieldSingletonEmptyCarrier
        (append ctx (ratup_fieldup_bracketing_endpoint_selector h k l s)) -> False :=
    fun singleton =>
      fieldSingletonEmptyCarrier_append_ratHistoryCarrier_absurd singleton selectedCarrier
  have leftContextEmpty :
      fieldSingletonEmptyCarrier
        (append (ratup_fieldup_bracketing_endpoint_selector h k l s) ctx) -> False :=
    fun singleton =>
      fieldSingletonEmptyCarrier_append_left_ratHistoryCarrier_absurd singleton selectedCarrier
  exact And.intro rightContextEmpty
    (And.intro leftContextEmpty
      (And.intro
        (fun classified => rightContextEmpty classified.left)
        (fun classified => leftContextEmpty classified.left)))

end BEDC.Derived.FieldUp
