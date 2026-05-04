import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_comp_middle_prefix_deterministic {p q a b c f g fg : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append q b) (append p c) g -> Cont f g fg ->
        CategoryHomCarrier (append p a) (append p c) fg -> hsame p q := by
  intro left right comp displayed
  have sameMiddle : hsame (append p b) (append q b) :=
    CategoryHomCarrier_comp_middle_object_deterministic left right comp displayed
  exact append_right_cancel (k := b) sameMiddle

end BEDC.Derived.FunctorUp
