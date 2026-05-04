import BEDC.Derived.NatTransUp
import BEDC.Derived.CategoryUp.MorphismEmptyEndpoint

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem NatTransPrefixComponentCarrier_component_empty_prefix_iff {p q a eta : BHist} :
    NatTransPrefixComponentCarrier p q a eta -> (hsame eta BHist.Empty <-> hsame p q) := by
  intro component
  constructor
  · intro componentEmpty
    have sameEndpoints :
        hsame (append p a) (append q a) :=
      (CategoryHomCarrier_morphism_empty_endpoint_iff component.right.right.right).mp componentEmpty
    exact append_right_cancel (k := a) sameEndpoints
  · intro samePrefix
    have sameEndpoints : hsame (append p a) (append q a) := by
      cases samePrefix
      rfl
    exact
      (CategoryHomCarrier_morphism_empty_endpoint_iff component.right.right.right).mpr sameEndpoints

end BEDC.Derived.NatTransUp
