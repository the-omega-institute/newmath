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

theorem CategoryHomCarrier_comp_endpoint_cycle_tails_empty {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg -> hsame a c ->
      hsame f BHist.Empty ∧ hsame g BHist.Empty ∧ hsame fg BHist.Empty := by
  intro left right comp sameEndpoint
  have compositeEmpty : hsame fg BHist.Empty :=
    CategoryHomCarrier_comp_endpoint_cycle_morphism_empty left right comp sameEndpoint
  have emptyComp : Cont f g BHist.Empty :=
    cont_result_hsame_transport comp compositeEmpty
  have tailsEmpty := cont_empty_result_inversion emptyComp
  exact And.intro tailsEmpty.left (And.intro tailsEmpty.right compositeEmpty)

theorem CategoryHomCarrier_comp_endpoint_cycle_boundary {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg -> hsame a c ->
      hsame f BHist.Empty ∧ hsame g BHist.Empty ∧ hsame fg BHist.Empty ∧ hsame a b ∧
        hsame b c := by
  intro left right comp sameEndpoint
  have tails := CategoryHomCarrier_comp_endpoint_cycle_tails_empty left right comp sameEndpoint
  exact ⟨tails.left, tails.right.left, tails.right.right,
    cont_deterministic (cont_right_unit a)
      (cont_hsame_transport (hsame_refl a) tails.left (hsame_refl b) left.right.right.right),
    cont_deterministic (cont_right_unit b)
      (cont_hsame_transport (hsame_refl b) tails.right.left (hsame_refl c)
        right.right.right.right)⟩

end BEDC.Derived.CategoryUp
