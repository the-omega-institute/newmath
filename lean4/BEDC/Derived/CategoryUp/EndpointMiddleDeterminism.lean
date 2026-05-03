import BEDC.Derived.CategoryUp.CompDeterminism

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_comp_middle_object_endpoint_hsame_deterministic
    {a a' b b' c c' f g fg : BHist} :
    hsame a a' -> hsame c c' -> CategoryHomCarrier a b f -> CategoryHomCarrier b' c g ->
      Cont f g fg -> CategoryHomCarrier a' c' fg -> hsame b b' := by
  intro sameSource sameTarget left right comp displayed
  cases sameSource
  cases sameTarget
  exact CategoryHomCarrier_comp_middle_object_deterministic left right comp displayed

end BEDC.Derived.CategoryUp
