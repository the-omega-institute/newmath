import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_comp_right_tail_fixed_left_identity {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame (append left.tail right.tail) right.tail ->
      hsame left.tail BHist.Empty ∧ hsame a b := by
  intro fixedRight
  have leftTailEmpty : hsame left.tail BHist.Empty :=
    cont_left_unit_unique (cont_intro fixedRight.symm)
  have sameSource : hsame a b := by
    have leftAsIdentity : Cont a BHist.Empty b :=
      cont_hsame_transport (hsame_refl a) leftTailEmpty (hsame_refl b) left.rel
    exact hsame_symm (cont_deterministic leftAsIdentity (cont_right_unit a))
  exact And.intro leftTailEmpty sameSource

theorem CategoryHomCarrier_comp_right_tail_fixed_left_identity {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      hsame fg g -> hsame f BHist.Empty ∧ hsame a b := by
  intro left _right comp fixedRight
  have leftTailEmpty : hsame f BHist.Empty :=
    cont_left_unit_unique (cont_result_hsame_transport comp fixedRight)
  have leftAsIdentity : Cont a BHist.Empty b :=
    cont_hsame_transport (hsame_refl a) leftTailEmpty (hsame_refl b)
      left.right.right.right
  exact And.intro leftTailEmpty
    (hsame_symm (cont_deterministic leftAsIdentity (cont_right_unit a)))

end BEDC.Derived.CategoryUp
