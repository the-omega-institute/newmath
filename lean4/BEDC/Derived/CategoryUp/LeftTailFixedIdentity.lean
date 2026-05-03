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

end BEDC.Derived.CategoryUp
