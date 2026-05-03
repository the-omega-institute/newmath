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

theorem ratup_fieldup_bracketing_selector_independence_package {h k l ctx : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier l ->
      ((RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l) ->
        forall s t : BEDC.FKernel.Mark.BMark,
          let a := ratup_fieldup_bracketing_endpoint_selector h k l s
          let b := ratup_fieldup_bracketing_endpoint_selector h k l t
          hsame a b ∧
            RatHistoryClassifier a b ∧
              (fieldSingletonEmptyCarrier (append ctx a) -> False) ∧
                (fieldSingletonEmptyCarrier (append a ctx) -> False) ∧
                  fieldSingletonEmptyNonZero (append ctx a) ∧
                    fieldSingletonEmptyNonZero (append a ctx) := by
  intro carrierH carrierK carrierL support s t
  have selectedSame :
      hsame (ratup_fieldup_bracketing_endpoint_selector h k l s)
        (ratup_fieldup_bracketing_endpoint_selector h k l t) :=
    ratup_fieldup_bracketing_endpoint_selector_same.right s t
  have selectedClassifier :
      RatHistoryClassifier (ratup_fieldup_bracketing_endpoint_selector h k l s)
        (ratup_fieldup_bracketing_endpoint_selector h k l t) :=
    ratup_fieldup_bracketing_selector_rat_classifier_coverage
      carrierH carrierK carrierL support s t
  have nonzeroRows :=
    ratup_fieldup_bracketing_selector_contextual_nonzero_package
      (ctx := ctx) carrierH carrierK carrierL support s
  exact And.intro selectedSame
    (And.intro selectedClassifier
      (And.intro nonzeroRows.left
        (And.intro nonzeroRows.right.left
          (And.intro nonzeroRows.right.right.left nonzeroRows.right.right.right))))

theorem ratup_fieldup_selector_pair_strict_exit_determinacy {h k l L R : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier l ->
      ((RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l) ->
        forall s t u v : BEDC.FKernel.Mark.BMark,
          let a := ratup_fieldup_bracketing_endpoint_selector h k l s
          let b := ratup_fieldup_bracketing_endpoint_selector h k l t
          let c := ratup_fieldup_bracketing_endpoint_selector h k l u
          let d := ratup_fieldup_bracketing_endpoint_selector h k l v
          RatHistoryClassifier a c ∧ RatHistoryClassifier b d ∧
            (fieldSingletonEmptyClassifier (append L a) (append R b) -> False) ∧
              (fieldSingletonEmptyClassifier (append L c) (append R d) -> False) ∧
                fieldSingletonEmptyNonZero (append L a) ∧
                  fieldSingletonEmptyNonZero (append c R) := by
  intro carrierH carrierK carrierL support s t u v
  have classifierAC :
      RatHistoryClassifier (ratup_fieldup_bracketing_endpoint_selector h k l s)
        (ratup_fieldup_bracketing_endpoint_selector h k l u) :=
    ratup_fieldup_bracketing_selector_rat_classifier_coverage
      carrierH carrierK carrierL support s u
  have classifierBD :
      RatHistoryClassifier (ratup_fieldup_bracketing_endpoint_selector h k l t)
        (ratup_fieldup_bracketing_endpoint_selector h k l v) :=
    ratup_fieldup_bracketing_selector_rat_classifier_coverage
      carrierH carrierK carrierL support t v
  have excludeAB :
      fieldSingletonEmptyClassifier
        (append L (ratup_fieldup_bracketing_endpoint_selector h k l s))
        (append R (ratup_fieldup_bracketing_endpoint_selector h k l t)) -> False :=
    ratup_fieldup_bracketing_selector_classifier_exclusion
      carrierH carrierK carrierL support s t L R
  have excludeCD :
      fieldSingletonEmptyClassifier
        (append L (ratup_fieldup_bracketing_endpoint_selector h k l u))
        (append R (ratup_fieldup_bracketing_endpoint_selector h k l v)) -> False :=
    ratup_fieldup_bracketing_selector_classifier_exclusion
      carrierH carrierK carrierL support u v L R
  have nonzeroA :=
    ratup_fieldup_bracketing_selector_contextual_nonzero_package
      (ctx := L) carrierH carrierK carrierL support s
  have nonzeroC :=
    ratup_fieldup_bracketing_selector_contextual_nonzero_package
      (ctx := R) carrierH carrierK carrierL support u
  exact And.intro classifierAC
    (And.intro classifierBD
      (And.intro excludeAB
        (And.intro excludeCD
          (And.intro nonzeroA.right.right.left nonzeroC.right.right.right))))

theorem ratup_fieldup_selector_complete_strict_exit_package {h k l : BHist}
    (carrierH : RatDenomUnitCarrier h) (carrierK : RatDenomUnitCarrier k)
    (carrierL : RatDenomUnitCarrier l)
    (support : (RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l)
    (s t : BEDC.FKernel.Mark.BMark) (L R : BHist) :
    let a := ratup_fieldup_bracketing_endpoint_selector h k l s
    let b := ratup_fieldup_bracketing_endpoint_selector h k l t
    RatHistoryCarrier a ∧ RatHistoryCarrier b ∧ RatHistoryClassifier a b ∧
      (fieldSingletonEmptyClassifier (append L a) (append R b) -> False) ∧
        fieldSingletonEmptyNonZero a ∧ fieldSingletonEmptyNonZero b := by
  dsimp
  have selectedA :
      RatHistoryCarrier (ratup_fieldup_bracketing_endpoint_selector h k l s) :=
    ratup_fieldup_bracketing_selector_rat_carrier_coverage
      carrierH carrierK carrierL support s
  have selectedB :
      RatHistoryCarrier (ratup_fieldup_bracketing_endpoint_selector h k l t) :=
    ratup_fieldup_bracketing_selector_rat_carrier_coverage
      carrierH carrierK carrierL support t
  have selectedClassifier :
      RatHistoryClassifier (ratup_fieldup_bracketing_endpoint_selector h k l s)
        (ratup_fieldup_bracketing_endpoint_selector h k l t) :=
    ratup_fieldup_bracketing_selector_rat_classifier_coverage
      carrierH carrierK carrierL support s t
  have singletonExit :
      fieldSingletonEmptyClassifier
        (append L (ratup_fieldup_bracketing_endpoint_selector h k l s))
        (append R (ratup_fieldup_bracketing_endpoint_selector h k l t)) -> False := by
    intro singleton
    exact fieldSingletonEmptyCarrier_append_ratHistoryCarrier_absurd singleton.left selectedA
  have nonzeroA :
      fieldSingletonEmptyNonZero (ratup_fieldup_bracketing_endpoint_selector h k l s) := by
    intro singleton
    exact RatHistoryCarrier_not_empty selectedA singleton.left
  have nonzeroB :
      fieldSingletonEmptyNonZero (ratup_fieldup_bracketing_endpoint_selector h k l t) := by
    intro singleton
    exact RatHistoryCarrier_not_empty selectedB singleton.left
  exact And.intro selectedA
    (And.intro selectedB
      (And.intro selectedClassifier
        (And.intro singletonExit (And.intro nonzeroA nonzeroB))))

theorem ratup_fieldup_bracketing_selector_complete_obstruction_package {h k l L R : BHist}
    (carrierH : RatDenomUnitCarrier h) (carrierK : RatDenomUnitCarrier k)
    (carrierL : RatDenomUnitCarrier l)
    (support : (RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l)
    (s t : BEDC.FKernel.Mark.BMark) :
    let a := ratup_fieldup_bracketing_endpoint_selector h k l s
    let b := ratup_fieldup_bracketing_endpoint_selector h k l t
    hsame a b ∧ RatDenomUnitClassifier a b ∧ RatHistoryClassifier a b ∧
      (fieldSingletonEmptyClassifier (append L a) (append R b) -> False) ∧
      (fieldSingletonEmptyCarrier (append L a) -> False) ∧
      fieldSingletonEmptyNonZero (append L a) ∧
      (fieldSingletonEmptyCarrier (append a R) -> False) ∧
      fieldSingletonEmptyNonZero (append a R) ∧
      (fieldSingletonEmptyCarrier (append L b) -> False) ∧
      fieldSingletonEmptyNonZero (append L b) ∧
      (fieldSingletonEmptyCarrier (append b R) -> False) ∧
      fieldSingletonEmptyNonZero (append b R) := by
  have selectedSame :
      hsame (ratup_fieldup_bracketing_endpoint_selector h k l s)
        (ratup_fieldup_bracketing_endpoint_selector h k l t) :=
    ratup_fieldup_bracketing_endpoint_selector_same.right s t
  have selectedHistory :
      RatHistoryClassifier (ratup_fieldup_bracketing_endpoint_selector h k l s)
        (ratup_fieldup_bracketing_endpoint_selector h k l t) :=
    ratup_fieldup_bracketing_selector_rat_classifier_coverage
      carrierH carrierK carrierL support s t
  have selectedDenom :
      RatDenomUnitClassifier (ratup_fieldup_bracketing_endpoint_selector h k l s)
        (ratup_fieldup_bracketing_endpoint_selector h k l t) :=
    And.intro (Or.inr selectedHistory.left)
      (And.intro (Or.inr selectedHistory.right.left) selectedHistory.right.right)
  have excluded :
      fieldSingletonEmptyClassifier
        (append L (ratup_fieldup_bracketing_endpoint_selector h k l s))
        (append R (ratup_fieldup_bracketing_endpoint_selector h k l t)) -> False :=
    ratup_fieldup_bracketing_selector_classifier_exclusion
      carrierH carrierK carrierL support s t L R
  have aLeft :=
    ratup_fieldup_bracketing_selector_contextual_nonzero_package
      (ctx := L) carrierH carrierK carrierL support s
  have aRight :=
    ratup_fieldup_bracketing_selector_contextual_nonzero_package
      (ctx := R) carrierH carrierK carrierL support s
  have bLeft :=
    ratup_fieldup_bracketing_selector_contextual_nonzero_package
      (ctx := L) carrierH carrierK carrierL support t
  have bRight :=
    ratup_fieldup_bracketing_selector_contextual_nonzero_package
      (ctx := R) carrierH carrierK carrierL support t
  exact And.intro selectedSame
    (And.intro selectedDenom
      (And.intro selectedHistory
        (And.intro excluded
          (And.intro aLeft.left
            (And.intro aLeft.right.right.left
              (And.intro aRight.right.left
                (And.intro aRight.right.right.right
                  (And.intro bLeft.left
                    (And.intro bLeft.right.right.left
                      (And.intro bRight.right.left bRight.right.right.right))))))))))

theorem ratup_fieldup_final_certificate_two_selector_noncollapse_boundary
    {h k l L R r : BHist} (carrierH : RatDenomUnitCarrier h)
    (carrierK : RatDenomUnitCarrier k) (carrierL : RatDenomUnitCarrier l)
    (support : (RatHistoryCarrier h ∨ RatHistoryCarrier k) ∨ RatHistoryCarrier l)
    (s t : BEDC.FKernel.Mark.BMark) :
    let a := ratup_fieldup_bracketing_endpoint_selector h k l s
    let b := ratup_fieldup_bracketing_endpoint_selector h k l t
    (hsame a b ∧ RatDenomUnitClassifier a b ∧ RatHistoryClassifier a b ∧
      (fieldSingletonEmptyClassifier (append L a) (append R b) -> False) ∧
      (fieldSingletonEmptyCarrier (append L a) -> False) ∧
      fieldSingletonEmptyNonZero (append L a) ∧
      (fieldSingletonEmptyCarrier (append a R) -> False) ∧
      fieldSingletonEmptyNonZero (append a R) ∧
      (fieldSingletonEmptyCarrier (append L b) -> False) ∧
      fieldSingletonEmptyNonZero (append L b) ∧
      (fieldSingletonEmptyCarrier (append b R) -> False) ∧
      fieldSingletonEmptyNonZero (append b R)) ∧
      (fieldSingletonEmptyCarrier (append r b) -> False) ∧
      (fieldSingletonEmptyCarrier (append b r) -> False) ∧
      fieldSingletonEmptyNonZero (append r b) ∧
      fieldSingletonEmptyNonZero (append b r) := by
  have obstruction :=
    ratup_fieldup_bracketing_selector_complete_obstruction_package
      (h := h) (k := k) (l := l) (L := L) (R := R)
      carrierH carrierK carrierL support s t
  have boundary :=
    ratup_fieldup_bracketing_selector_contextual_nonzero_package
      (h := h) (k := k) (l := l) (ctx := r) carrierH carrierK carrierL support t
  exact And.intro obstruction
    (And.intro boundary.left
      (And.intro boundary.right.left
        (And.intro boundary.right.right.left boundary.right.right.right)))

end BEDC.Derived.FieldUp
