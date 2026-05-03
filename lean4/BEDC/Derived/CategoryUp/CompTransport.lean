import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_comp_hsame_transport {a a' b c c' f g fg fg' : BHist} :
    hsame a a' -> hsame c c' -> hsame fg fg' ->
      CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
        CategoryHomCarrier a' c' fg' := by
  intro sameSource sameTarget sameComposite left right comp
  have composite : CategoryHomCarrier a c fg := CategoryHomCarrier_comp_closed left right comp
  exact CategoryHomCarrier_hsame_transport sameSource sameTarget sameComposite composite

end BEDC.Derived.CategoryUp
