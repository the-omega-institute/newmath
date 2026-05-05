import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_opposite_comp_assoc_closed
    {a b c d f g h fg gh left right : BHist} :
    CategoryHomCarrier b a f -> CategoryHomCarrier c b g -> CategoryHomCarrier d c h ->
      Cont g f fg -> Cont h g gh -> Cont h fg left -> Cont gh f right ->
        CategoryHomCarrier d a left ∧ CategoryHomCarrier d a right ∧ hsame left right := by
  intro first second third fgRel ghRel leftRel rightRel
  have closed :
      CategoryHomCarrier d a right ∧ CategoryHomCarrier d a left ∧ hsame right left :=
    CategoryHomCarrier_comp_assoc_closed third second first ghRel fgRel rightRel leftRel
  exact And.intro closed.right.left
    (And.intro closed.left (hsame_symm closed.right.right))

end BEDC.Derived.CategoryUp
