import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_unary_suffix_comp_assoc_reflects
    {p q a b c d f g h fg gh left right : BHist} :
    CategoryHomCarrier (append (append p a) q) (append (append p b) q) f ->
      CategoryHomCarrier (append (append p b) q) (append (append p c) q) g ->
        CategoryHomCarrier (append (append p c) q) (append (append p d) q) h ->
          Cont f g fg -> Cont g h gh -> Cont fg h left -> Cont f gh right ->
            CategoryHomCarrier a d left ∧ CategoryHomCarrier a d right ∧ hsame left right := by
  intro first second third fgRel ghRel leftRel rightRel
  have firstCentral := (CategoryHomCarrier_unary_context_iff.mp first).right.right
  have secondCentral := (CategoryHomCarrier_unary_context_iff.mp second).right.right
  have thirdCentral := (CategoryHomCarrier_unary_context_iff.mp third).right.right
  exact
    CategoryHomCarrier_comp_assoc_closed
      firstCentral secondCentral thirdCentral fgRel ghRel leftRel rightRel

end BEDC.Derived.FunctorUp
