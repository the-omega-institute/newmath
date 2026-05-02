import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_empty_source_comp_result_hsame {b c f g fg : BHist} :
    CategoryHomCarrier BHist.Empty b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier BHist.Empty c fg ∧ hsame fg c := by
  intro left right comp
  have compositeCarrier : CategoryHomCarrier BHist.Empty c fg :=
    CategoryHomCarrier_comp_closed left right comp
  exact And.intro compositeCarrier (CategoryHomCarrier_empty_source_iff.mp compositeCarrier).right

end BEDC.Derived.CategoryUp
