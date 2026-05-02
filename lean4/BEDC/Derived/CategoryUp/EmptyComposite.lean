import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_empty_composite_factors {a b c f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g BHist.Empty ->
      hsame f BHist.Empty /\ hsame g BHist.Empty /\ hsame a b /\ hsame b c := by
  intro left right comp
  have emptyFactors := cont_empty_result_inversion comp
  have leftEmptyCarrier : CategoryHomCarrier a b BHist.Empty :=
    CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) emptyFactors.left left
  have rightEmptyCarrier : CategoryHomCarrier b c BHist.Empty :=
    CategoryHomCarrier_hsame_transport (hsame_refl b) (hsame_refl c) emptyFactors.right right
  have leftEndpoint := Iff.mp CategoryHomCarrier_empty_identity_iff leftEmptyCarrier
  have rightEndpoint := Iff.mp CategoryHomCarrier_empty_identity_iff rightEmptyCarrier
  exact And.intro emptyFactors.left
    (And.intro emptyFactors.right
      (And.intro leftEndpoint.right.right rightEndpoint.right.right))

end BEDC.Derived.CategoryUp
