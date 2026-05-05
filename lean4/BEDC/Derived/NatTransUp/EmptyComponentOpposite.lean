import BEDC.Derived.NatTransUp
import BEDC.Derived.NatTransUp.EmptyVertComp
import BEDC.Derived.CategoryUp.EmptyComposite

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem NatTransPrefixComponentCarrier_empty_component_opposite_closed {p q a eta : BHist} :
    NatTransPrefixComponentCarrier p q a eta -> hsame eta BHist.Empty ->
      NatTransPrefixComponentCarrier q p a eta := by
  intro component etaEmpty
  cases etaEmpty
  have identityData :=
    (NatTransPrefixComponentCarrier_empty_identity_iff (p := p) (q := q) (a := a)).mp
      component
  exact
    (NatTransPrefixComponentCarrier_empty_identity_iff (p := q) (q := p) (a := a)).mpr
        (And.intro identityData.right.left
          (And.intro identityData.left
            (And.intro identityData.right.right.left
              (hsame_symm identityData.right.right.right))))

theorem NatTransPrefixComponentCarrier_vert_comp_empty_result_opposite_closed
    {p q r a eta theta : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta -> Cont eta theta BHist.Empty ->
        NatTransPrefixComponentCarrier r p a BHist.Empty := by
  intro left right comp
  have closed : NatTransPrefixComponentCarrier p r a BHist.Empty :=
    NatTransPrefixComponentCarrier_vert_comp_closed left right comp
  exact
    NatTransPrefixComponentCarrier_empty_component_opposite_closed
      closed (hsame_refl BHist.Empty)

theorem NatTransPrefixComponentCarrier_vert_comp_empty_result_prefixes_hsame
    {p q r a eta theta : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta -> Cont eta theta BHist.Empty ->
        hsame p q ∧ hsame q r := by
  intro left right comp
  have base :=
    (CategoryHomCarrier_empty_composite_iff left.right.right.right right.right.right.right).mp comp
  exact
    And.intro
      (append_right_cancel (k := a) base.right.right.left)
      (append_right_cancel (k := a) base.right.right.right)

theorem NatTransPrefixComponentCarrier_vert_comp_empty_result_components_opposite_closed
    {p q r a eta theta : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta -> Cont eta theta BHist.Empty ->
        NatTransPrefixComponentCarrier q p a eta ∧
          NatTransPrefixComponentCarrier r q a theta := by
  intro left right comp
  have emptyData := Iff.mp (NatTransPrefixComponentCarrier_vert_comp_empty_iff left right) comp
  exact
    And.intro
      (NatTransPrefixComponentCarrier_empty_component_opposite_closed left emptyData.left)
      (NatTransPrefixComponentCarrier_empty_component_opposite_closed right emptyData.right.left)

end BEDC.Derived.NatTransUp
