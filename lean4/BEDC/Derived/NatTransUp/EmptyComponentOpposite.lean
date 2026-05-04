import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist

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

end BEDC.Derived.NatTransUp
