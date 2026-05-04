import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_comp_assoc_empty_result_components
    {a b c d f g h fg gh left right : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> CategoryHomCarrier c d h ->
      Cont f g fg -> Cont g h gh -> Cont fg h left -> Cont f gh right ->
        CategoryHomCarrier a d BHist.Empty ->
          hsame left BHist.Empty ∧ hsame right BHist.Empty ∧ hsame a d := by
  intro first second third fgRel ghRel leftRel rightRel emptyDisplayed
  have displayed :=
    CategoryHomCarrier_comp_assoc_displayed_deterministic
      first second third fgRel ghRel leftRel rightRel emptyDisplayed
  have endpoints :=
    (CategoryHomCarrier_empty_identity_iff (a := a) (b := d)).mp emptyDisplayed
  exact And.intro displayed.left (And.intro displayed.right endpoints.right.right)

end BEDC.Derived.CategoryUp
