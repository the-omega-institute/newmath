import BEDC.Derived.CategoryUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem CategoryHomCarrier_cycle_tails_empty {a b f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b a g ->
      hsame a b ∧ hsame f BHist.Empty ∧ hsame g BHist.Empty := by
  intro left right
  have sameEndpoint : hsame a b :=
    cont_mutual_extension_hsame left.right.right.right right.right.right.right
  have tailsEmpty : hsame f BHist.Empty ∧ hsame g BHist.Empty :=
    cont_mutual_extension_tails_empty left.right.right.right right.right.right.right
  exact And.intro sameEndpoint tailsEmpty

theorem CategoryHomCarrier_e1_morphism_cycle_absurd {a b k g : BHist} :
    CategoryHomCarrier a b (BHist.e1 k) -> CategoryHomCarrier b a g -> False := by
  intro left right
  have cycle := CategoryHomCarrier_cycle_tails_empty left right
  exact not_hsame_e1_empty cycle.right.left

end BEDC.Derived.CategoryUp
