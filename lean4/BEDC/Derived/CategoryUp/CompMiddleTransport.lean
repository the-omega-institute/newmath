import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist BEDC.FKernel.Cont BEDC.FKernel.Unary

theorem CategoryHomCarrier_comp_middle_hsame_closed {a b b' c f g fg : BHist} :
    hsame b b' -> CategoryHomCarrier a b f -> CategoryHomCarrier b' c g ->
      Cont f g fg -> CategoryHomCarrier a c fg := by
  intro sameMiddle left right comp
  have movedRight : CategoryHomCarrier b c g :=
    CategoryHomCarrier_hsame_transport (hsame_symm sameMiddle) (hsame_refl c) (hsame_refl g)
      right
  exact CategoryHomCarrier_comp_closed left movedRight comp

end BEDC.Derived.CategoryUp
