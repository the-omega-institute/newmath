import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_comp_tail_exact_iff {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g ->
      (CategoryHomCarrier a c fg <-> Cont f g fg) := by
  intro left right
  constructor
  · intro displayed
    exact cont_composite_tail_unique left.right.right.right right.right.right.right
      displayed.right.right.right
  · intro comp
    exact CategoryHomCarrier_comp_closed left right comp

end BEDC.Derived.CategoryUp
