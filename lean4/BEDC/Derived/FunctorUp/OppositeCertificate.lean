import BEDC.Derived.CategoryUp.OppositeAssoc
import BEDC.Derived.FunctorUp.PrefixCarrier

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem PrefixFunctorCarrier_opposite_comp_assoc_public_readback
    {p a b c d f g h gf hg left right : BHist} :
    PrefixFunctorCarrier p -> CategoryHomCarrier b a f -> CategoryHomCarrier c b g ->
      CategoryHomCarrier d c h -> Cont g f gf -> Cont h g hg -> Cont h gf left ->
        Cont hg f right ->
          CategoryHomCarrier (append p d) (append p a) left ∧
            CategoryHomCarrier (append p d) (append p a) right ∧ hsame left right := by
  intro prefixCarrier first second third gfRel hgRel leftRel rightRel
  have oppositeClosed :=
    CategoryHomCarrier_opposite_comp_assoc_closed
      first second third gfRel hgRel leftRel rightRel
  exact
    And.intro
      (prefixCarrier.hom_preserves oppositeClosed.left)
      (And.intro
        (prefixCarrier.hom_preserves oppositeClosed.right.left)
        oppositeClosed.right.right)

end BEDC.Derived.FunctorUp
