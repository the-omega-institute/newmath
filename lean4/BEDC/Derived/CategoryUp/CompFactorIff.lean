import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_comp_right_factor_iff {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier a c fg ->
      (CategoryHomCarrier b c g <-> Cont f g fg) := by
  intro left displayed
  constructor
  · intro right
    exact cont_composite_tail_unique left.right.right.right right.right.right.right
      displayed.right.right.right
  · intro comp
    exact CategoryHomCarrier_comp_right_factor left comp displayed

theorem CategoryHomCarrier_comp_left_factor_iff {a b c f g fg : BHist} :
    CategoryHomCarrier b c g -> CategoryHomCarrier a c fg ->
      (CategoryHomCarrier a b f <-> Cont f g fg) := by
  intro right displayed
  constructor
  · intro left
    exact cont_composite_tail_unique left.right.right.right right.right.right.right
      displayed.right.right.right
  · intro comp
    exact CategoryHomCarrier_comp_left_factor right comp displayed

end BEDC.Derived.CategoryUp
