import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem NatTransPrefixComponentCarrier_empty_object_iff {p q eta : BHist} :
    NatTransPrefixComponentCarrier p q BHist.Empty eta ↔
      UnaryHistory p ∧ UnaryHistory q ∧ CategoryHomCarrier p q eta := by
  constructor
  · intro component
    exact
      And.intro component.left
        (And.intro component.right.left
          (CategoryHomCarrier_hsame_transport (append_empty_right p) (append_empty_right q)
            (hsame_refl eta) component.right.right.right))
  · intro data
    exact
      And.intro data.left
        (And.intro data.right.left
          (And.intro unary_empty
            (CategoryHomCarrier_hsame_transport (hsame_symm (append_empty_right p))
              (hsame_symm (append_empty_right q)) (hsame_refl eta) data.right.right)))

end BEDC.Derived.NatTransUp
