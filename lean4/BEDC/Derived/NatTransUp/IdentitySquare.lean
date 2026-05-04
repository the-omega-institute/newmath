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

theorem NatTransPrefixComponentCarrier_vert_comp_right_identity_empty_result_iff
    {p q a eta right : BHist} :
    NatTransPrefixComponentCarrier p q a eta -> Cont eta BHist.Empty right ->
      (hsame right BHist.Empty ↔ hsame eta BHist.Empty ∧ hsame p q) := by
  intro component rightRel
  have closed :=
    NatTransPrefixComponentCarrier_vert_comp_right_identity_closed component rightRel
  constructor
  · intro rightEmpty
    have etaEmpty : hsame eta BHist.Empty :=
      hsame_trans (hsame_symm closed.right) rightEmpty
    have emptyComponent : NatTransPrefixComponentCarrier p q a BHist.Empty := by
      cases rightEmpty
      exact closed.left
    have identityData :=
      Iff.mp NatTransPrefixComponentCarrier_empty_identity_iff emptyComponent
    exact And.intro etaEmpty identityData.right.right.right
  · intro data
    cases data.left
    exact cont_deterministic rightRel (cont_right_unit BHist.Empty)

end BEDC.Derived.NatTransUp
