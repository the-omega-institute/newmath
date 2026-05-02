import BEDC.Derived.CategoryUp.TailCommClosed

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_comp_same_middle_factors_deterministic {a b c f g f' g' fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier a b f' -> CategoryHomCarrier b c g' -> Cont f' g' fg ->
        hsame f f' ∧ hsame g g' := by
  intro left _right comp left' _right' comp'
  have sameF : hsame f f' := CategoryHomCarrier_morphism_deterministic left left'
  have sameG : hsame g g' := by
    cases sameF
    exact cont_left_cancel comp comp'
  exact And.intro sameF sameG

theorem CategoryHomCarrier_comp_right_factor_endpoint_deterministic {a b b' c f g g' fg : BHist} :
    CategoryHomCarrier a b f -> Cont f g fg -> CategoryHomCarrier a c fg ->
      Cont f g' fg -> CategoryHomCarrier b' c g' -> hsame b b' ∧ hsame g g' := by
  intro left comp displayed comp' right'
  have right : CategoryHomCarrier b c g :=
    CategoryHomCarrier_comp_right_factor left comp displayed
  have sameG : hsame g g' := cont_left_cancel comp comp'
  have transportedRight : CategoryHomCarrier b c g' :=
    CategoryHomCarrier_hsame_transport (hsame_refl b) (hsame_refl c) sameG right
  have sameSource : hsame b b' :=
    CategoryHomCarrier_source_deterministic transportedRight right'
  exact And.intro sameSource sameG

theorem CategoryHomCarrier_comp_right_factor_target_deterministic {a b c c' f g g' fg : BHist} :
    CategoryHomCarrier a b f -> Cont f g fg -> CategoryHomCarrier a c fg ->
      Cont f g' fg -> CategoryHomCarrier b c' g' -> hsame c c' ∧ hsame g g' := by
  intro left comp displayed comp' right'
  have right : CategoryHomCarrier b c g :=
    CategoryHomCarrier_comp_right_factor left comp displayed
  have sameG : hsame g g' := cont_left_cancel comp comp'
  have transportedRight : CategoryHomCarrier b c g' :=
    CategoryHomCarrier_hsame_transport (hsame_refl b) (hsame_refl c) sameG right
  have sameTarget : hsame c c' :=
    CategoryHomCarrier_target_deterministic transportedRight right'
  exact And.intro sameTarget sameG

theorem CategoryHomCarrier_comp_left_factor_endpoint_deterministic {a b b' c f f' g fg : BHist} :
    CategoryHomCarrier b c g -> Cont f g fg -> CategoryHomCarrier a c fg ->
      Cont f' g fg -> CategoryHomCarrier a b' f' -> hsame b b' ∧ hsame f f' := by
  intro right comp displayed comp' left'
  have left : CategoryHomCarrier a b f :=
    CategoryHomCarrier_comp_left_factor right comp displayed
  have sameF : hsame f f' := cont_right_cancel comp comp'
  have transportedLeft : CategoryHomCarrier a b f' :=
    CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) sameF left
  have sameTarget : hsame b b' :=
    CategoryHomCarrier_target_deterministic transportedLeft left'
  exact And.intro sameTarget sameF

theorem CategoryHomCarrier_comp_result_hsame_congruence {a b c f g f' g' fg fg' : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier a b f' -> CategoryHomCarrier b c g' -> Cont f' g' fg' ->
        hsame fg fg' := by
  intro left right comp left' right' comp'
  have composite : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right comp
  have composite' : CategoryHomCarrier a c fg' :=
    CategoryHomCarrier_comp_closed left' right' comp'
  exact CategoryHomCarrier_morphism_deterministic composite composite'

theorem CategoryHomCarrier_tail_comm_target_deterministic {a b c d f g fg gf : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg -> Cont g f gf ->
      CategoryHomCarrier a d gf -> hsame c d := by
  intro left right fgRel gfRel displayed
  have closed :=
    CategoryHomCarrier_tail_comm_closed left right fgRel gfRel
  exact CategoryHomCarrier_target_deterministic closed.right.left displayed

theorem CategoryHomCarrier_comp_left_factor_source_deterministic {a a' b c f f' g fg : BHist} :
    CategoryHomCarrier b c g -> Cont f g fg -> CategoryHomCarrier a c fg ->
      Cont f' g fg -> CategoryHomCarrier a' b f' -> hsame a a' ∧ hsame f f' := by
  intro right comp displayed comp' left'
  have left : CategoryHomCarrier a b f :=
    CategoryHomCarrier_comp_left_factor right comp displayed
  have sameF : hsame f f' := cont_right_cancel comp comp'
  have transportedLeft : CategoryHomCarrier a b f' :=
    CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) sameF left
  have sameSource : hsame a a' :=
    CategoryHomCarrier_source_deterministic transportedLeft left'
  exact And.intro sameSource sameF

end BEDC.Derived.CategoryUp
