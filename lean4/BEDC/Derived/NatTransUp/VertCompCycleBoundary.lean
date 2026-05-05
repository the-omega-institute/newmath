import BEDC.Derived.NatTransUp
import BEDC.Derived.CategoryUp.CompCycleResult

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem NatTransPrefixComponentCarrier_vert_comp_endpoint_cycle_boundary
    {p q r a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta -> Cont eta theta composite -> hsame p r ->
        hsame eta BHist.Empty ∧ hsame theta BHist.Empty ∧
          hsame composite BHist.Empty ∧ hsame p q ∧ hsame q r := by
  intro left right comp samePrefix
  have sameComponentEndpoint : hsame (append p a) (append r a) := by
    cases samePrefix
    exact hsame_refl (append p a)
  have boundary :=
    CategoryHomCarrier_comp_endpoint_cycle_boundary left.right.right.right right.right.right.right
      comp sameComponentEndpoint
  exact
    And.intro boundary.left
      (And.intro boundary.right.left
        (And.intro boundary.right.right.left
          (And.intro
            (append_right_cancel (k := a) boundary.right.right.right.left)
            (append_right_cancel (k := a) boundary.right.right.right.right))))

end BEDC.Derived.NatTransUp
