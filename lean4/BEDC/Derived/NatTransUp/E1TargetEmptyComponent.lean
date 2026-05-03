import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NatTransPrefixComponentCarrier_e1_target_empty_component_iff {p q a : BHist} :
    NatTransPrefixComponentCarrier p (BHist.e1 q) a BHist.Empty ↔
      UnaryHistory q ∧ UnaryHistory a ∧ p = BHist.e1 q := by
  constructor
  · intro component
    have identityData :=
      (NatTransPrefixComponentCarrier_empty_identity_iff
        (p := p) (q := BHist.e1 q) (a := a)).mp component
    exact
      And.intro (unary_e1_inversion identityData.right.left)
        (And.intro identityData.right.right.left identityData.right.right.right)
  · intro data
    cases data.right.right
    exact
      (NatTransPrefixComponentCarrier_empty_identity_iff
        (p := BHist.e1 q) (q := BHist.e1 q) (a := a)).mpr
        (And.intro (unary_e1_closed data.left)
          (And.intro (unary_e1_closed data.left)
            (And.intro data.right.left (hsame_refl (BHist.e1 q)))))

end BEDC.Derived.NatTransUp
