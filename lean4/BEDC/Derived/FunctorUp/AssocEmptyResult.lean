import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_comp_assoc_empty_result_components
    {p a b c d f g h fg gh left right : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g ->
      CategoryHomCarrier c d h -> Cont f g fg -> Cont g h gh -> Cont fg h left ->
        Cont f gh right ->
          CategoryHomCarrier (append p a) (append p d) BHist.Empty ->
            hsame left BHist.Empty ∧ hsame right BHist.Empty ∧ hsame a d := by
  intro prefixCarrier first second third fgRel ghRel leftRel rightRel emptyDisplayed
  have displayed :=
    FunctorPrefixHomCarrier_comp_assoc_displayed_deterministic
      prefixCarrier first second third fgRel ghRel leftRel rightRel emptyDisplayed
  have endpoints :=
    (FunctorPrefixHomCarrier_empty_identity_iff (p := p) (a := a) (b := d)).mp
      emptyDisplayed
  exact And.intro displayed.left (And.intro displayed.right endpoints.right.right)

end BEDC.Derived.FunctorUp
