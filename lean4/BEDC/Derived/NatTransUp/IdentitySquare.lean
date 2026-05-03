import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.FunctorUp

theorem NatTransPrefixIdentity_identity_component_square_public_readback
    {p a id left right displayed : BHist} :
    UnaryHistory p -> UnaryHistory a -> Cont BHist.Empty BHist.Empty id ->
      Cont id BHist.Empty left -> Cont BHist.Empty id right ->
        NatTransPrefixComponentCarrier p p a displayed -> hsame left displayed ∧ hsame right displayed := by
  intro prefixCarrier sourceCarrier idRel leftRel rightRel displayedCarrier
  have closed :=
    NatTransPrefixIdentity_identity_component_square_closed
      prefixCarrier sourceCarrier idRel leftRel rightRel
  exact
    And.intro
      (CategoryHomCarrier_morphism_deterministic
        closed.left displayedCarrier.right.right.right)
      (CategoryHomCarrier_morphism_deterministic
        closed.right.left displayedCarrier.right.right.right)

end BEDC.Derived.NatTransUp
