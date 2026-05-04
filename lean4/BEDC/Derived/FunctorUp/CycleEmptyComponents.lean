import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_cycle_empty_components {p q a f g : BHist} :
    CategoryHomCarrier (append p a) (append q a) f ->
      CategoryHomCarrier (append q a) (append p a) g ->
        CategoryHomCarrier (append p a) (append q a) BHist.Empty ∧
          CategoryHomCarrier (append q a) (append p a) BHist.Empty ∧ hsame p q := by
  intro left right
  have cycle := CategoryHomCarrier_cycle_tails_empty left right
  exact
    And.intro
      (CategoryHomCarrier_hsame_transport (hsame_refl (append p a))
        (hsame_refl (append q a)) cycle.right.left left)
      (And.intro
        (CategoryHomCarrier_hsame_transport (hsame_refl (append q a))
          (hsame_refl (append p a)) cycle.right.right right)
        (append_right_cancel (k := a) cycle.left))

end BEDC.Derived.FunctorUp
