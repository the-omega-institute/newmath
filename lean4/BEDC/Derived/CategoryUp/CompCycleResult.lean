import BEDC.Derived.CategoryUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_comp_cycle_result_empty {a b f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b a g -> Cont f g fg ->
      hsame fg BHist.Empty := by
  intro left right comp
  have tailsEmpty : hsame f BHist.Empty ∧ hsame g BHist.Empty :=
    cont_mutual_extension_tails_empty left.right.right.right right.right.right.right
  have emptyComp : Cont BHist.Empty BHist.Empty fg :=
    cont_hsame_transport tailsEmpty.left tailsEmpty.right (hsame_refl fg) comp
  exact cont_left_unit_result emptyComp

end BEDC.Derived.CategoryUp
