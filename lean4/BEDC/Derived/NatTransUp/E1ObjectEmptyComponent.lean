import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NatTransPrefixComponentCarrier_e1_object_empty_component_iff {p q a : BHist} :
    NatTransPrefixComponentCarrier p q (BHist.e1 a) BHist.Empty ↔
      UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory a ∧ hsame p q := by
  constructor
  · intro component
    have identityData :=
      (NatTransPrefixComponentCarrier_empty_identity_iff
        (p := p) (q := q) (a := BHist.e1 a)).mp component
    exact
      And.intro identityData.left
        (And.intro identityData.right.left
          (And.intro (unary_e1_inversion identityData.right.right.left)
            identityData.right.right.right))
  · intro data
    exact
      (NatTransPrefixComponentCarrier_empty_identity_iff
        (p := p) (q := q) (a := BHist.e1 a)).mpr
        (And.intro data.left
          (And.intro data.right.left
            (And.intro (unary_e1_closed data.right.right.left) data.right.right.right)))

end BEDC.Derived.NatTransUp
