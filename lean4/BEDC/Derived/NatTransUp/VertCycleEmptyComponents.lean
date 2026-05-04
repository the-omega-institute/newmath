import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem NatTransPrefixComponentCarrier_vert_cycle_empty_components {p q a eta theta : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q p a theta ->
        NatTransPrefixComponentCarrier p q a BHist.Empty ∧
          NatTransPrefixComponentCarrier q p a BHist.Empty ∧ hsame p q := by
  intro left right
  have cycle :=
    CategoryHomCarrier_cycle_tails_empty left.right.right.right right.right.right.right
  exact
    And.intro
      (And.intro left.left
        (And.intro left.right.left
          (And.intro left.right.right.left
            (CategoryHomCarrier_hsame_transport (hsame_refl (append p a))
              (hsame_refl (append q a)) cycle.right.left left.right.right.right))))
      (And.intro
        (And.intro right.left
          (And.intro right.right.left
            (And.intro right.right.right.left
              (CategoryHomCarrier_hsame_transport (hsame_refl (append q a))
                (hsame_refl (append p a)) cycle.right.right right.right.right.right))))
        (append_right_cancel (k := a) cycle.left))

end BEDC.Derived.NatTransUp
