import BEDC.Derived.CategoryUp.EmptySourceComposite

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_empty_source_comp_target_hsame {b c f g fg : BHist} :
    CategoryHomCarrier BHist.Empty b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      hsame fg c := by
  intro left right comp
  have leftReadback := CategoryHomCarrier_empty_source_iff.mp left
  have shiftedComp : Cont b g fg :=
    cont_hsame_transport leftReadback.right (hsame_refl g) (hsame_refl fg) comp
  exact cont_deterministic shiftedComp right.right.right.right

theorem CategoryHomCarrier_empty_source_comp_empty_result_iff {b c f g fg : BHist} :
    CategoryHomCarrier BHist.Empty b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      (hsame fg BHist.Empty <-> hsame c BHist.Empty) := by
  intro left right comp
  have sameResultTarget : hsame fg c :=
    CategoryHomCarrier_empty_source_comp_target_hsame left right comp
  constructor
  · intro resultEmpty
    exact hsame_trans (hsame_symm sameResultTarget) resultEmpty
  · intro targetEmpty
    exact hsame_trans sameResultTarget targetEmpty

end BEDC.Derived.CategoryUp
