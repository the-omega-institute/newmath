import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_opposite_comp_assoc_closed
    {a b c d f g h gf hg left right : BHist} :
    CategoryHomCarrier b a f -> CategoryHomCarrier c b g -> CategoryHomCarrier d c h ->
      Cont g f gf -> Cont h g hg -> Cont h gf left -> Cont hg f right ->
        CategoryHomCarrier d a left ∧ CategoryHomCarrier d a right ∧ hsame left right := by
  intro first second third gfRel hgRel leftRel rightRel
  have closed :=
    CategoryHomCarrier_comp_assoc_closed third second first hgRel gfRel rightRel leftRel
  exact And.intro closed.right.left
    (And.intro closed.left (hsame_symm closed.right.right))

end BEDC.Derived.CategoryUp
