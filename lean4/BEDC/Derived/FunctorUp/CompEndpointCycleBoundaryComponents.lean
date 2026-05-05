import BEDC.Derived.FunctorUp
import BEDC.Derived.CategoryUp.CompCycleResult

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_comp_endpoint_cycle_boundary_components
    {p a b c f g fg : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append p b) (append p c) g -> Cont f g fg -> hsame a c ->
        hsame f BHist.Empty ∧ hsame g BHist.Empty ∧ hsame fg BHist.Empty ∧
          hsame a b ∧ hsame b c := by
  intro left right comp sameEndpoint
  have samePrefixedEndpoint : hsame (append p a) (append p c) := by
    cases sameEndpoint
    exact hsame_refl (append p a)
  have boundary :=
    CategoryHomCarrier_comp_endpoint_cycle_boundary left right comp samePrefixedEndpoint
  exact
    And.intro boundary.left
      (And.intro boundary.right.left
        (And.intro boundary.right.right.left
          (And.intro
            (append_left_cancel (h := p) boundary.right.right.right.left)
            (append_left_cancel (h := p) boundary.right.right.right.right))))

end BEDC.Derived.FunctorUp
