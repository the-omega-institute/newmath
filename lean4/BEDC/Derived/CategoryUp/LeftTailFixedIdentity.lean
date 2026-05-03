import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_comp_left_tail_fixed_right_identity {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame (append left.tail right.tail) left.tail -> hsame right.tail BHist.Empty ∧ hsame b c := by
  intro fixedLeft
  have rightTailEmpty : hsame right.tail BHist.Empty :=
    cont_right_unit_unique (cont_intro fixedLeft.symm)
  have sameTarget : hsame b c := by
    have rightAsIdentity : Cont b BHist.Empty c :=
      cont_hsame_transport (hsame_refl b) rightTailEmpty (hsame_refl c) right.rel
    exact hsame_symm (cont_deterministic rightAsIdentity (cont_right_unit b))
  exact And.intro rightTailEmpty sameTarget

theorem CategoryHomCarrier_right_append_fixed_identity_iff {a b f g : BHist}
    (hom : CategoryHomCarrier a b f) :
    hsame (append f g) g <-> hsame f BHist.Empty /\ hsame a b := by
  constructor
  · intro fixed
    have fixedCont : Cont f g g := cont_intro fixed.symm
    have tailEmpty : hsame f BHist.Empty := cont_left_unit_unique fixedCont
    have identityRel : Cont a BHist.Empty b :=
      cont_hsame_transport (hsame_refl a) tailEmpty (hsame_refl b) hom.right.right.right
    have sameTarget : hsame a b :=
      hsame_symm (cont_deterministic identityRel (cont_right_unit a))
    exact And.intro tailEmpty sameTarget
  · intro data
    cases data.left
    exact append_empty_left g

theorem CategoryHomCarrier_left_append_fixed_identity_iff {a b f g : BHist}
    (hom : CategoryHomCarrier a b f) :
    hsame (append g f) g <-> hsame f BHist.Empty /\ hsame a b := by
  constructor
  · intro fixed
    have tailEmpty : hsame f BHist.Empty :=
      append_left_cancel (h := g) (fixed.trans (append_empty_right g).symm)
    have identityRel : Cont a BHist.Empty b :=
      cont_hsame_transport (hsame_refl a) tailEmpty (hsame_refl b) hom.right.right.right
    have sameTarget : hsame a b :=
      hsame_symm (cont_deterministic identityRel (cont_right_unit a))
    exact And.intro tailEmpty sameTarget
  · intro data
    cases data.left
    exact append_empty_right g

end BEDC.Derived.CategoryUp
