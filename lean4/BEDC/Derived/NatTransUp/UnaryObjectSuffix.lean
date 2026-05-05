import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem NatTransPrefixComponentCarrier_unary_object_suffix_iff {p q a eta : BHist} :
    NatTransPrefixComponentCarrier p q a eta ↔
      UnaryHistory a ∧ CategoryHomCarrier p q eta := by
  constructor
  · intro component
    have suffixData :=
      (CategoryHomCarrier_unary_suffix_iff (q := a) (a := p) (b := q) (f := eta)).mp
        component.right.right.right
    exact And.intro suffixData.left suffixData.right
  · intro data
    have suffixedHom :
        CategoryHomCarrier (append p a) (append q a) eta :=
      (CategoryHomCarrier_unary_suffix_iff (q := a) (a := p) (b := q) (f := eta)).mpr
        (And.intro data.left data.right)
    exact And.intro data.right.left
      (And.intro data.right.right.left (And.intro data.left suffixedHom))

end BEDC.Derived.NatTransUp
