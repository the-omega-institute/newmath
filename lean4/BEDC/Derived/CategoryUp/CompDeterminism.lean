import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_comp_same_middle_factors_deterministic {a b c f g f' g' fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier a b f' -> CategoryHomCarrier b c g' -> Cont f' g' fg ->
        hsame f f' ∧ hsame g g' := by
  intro left _right comp left' _right' comp'
  have sameF : hsame f f' := CategoryHomCarrier_morphism_deterministic left left'
  have sameG : hsame g g' := by
    cases sameF
    exact cont_left_cancel comp comp'
  exact And.intro sameF sameG

end BEDC.Derived.CategoryUp
