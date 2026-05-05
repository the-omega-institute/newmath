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

theorem NatTransPrefixComponentCarrier_vert_comp_left_identity_empty_result_iff
    {p q a eta left : BHist} :
    NatTransPrefixComponentCarrier p q a eta -> Cont BHist.Empty eta left ->
      (hsame left BHist.Empty ↔ hsame eta BHist.Empty ∧ hsame p q) := by
  intro component leftRel
  have closed :=
    NatTransPrefixComponentCarrier_vert_comp_left_identity_closed component leftRel
  constructor
  · intro leftEmpty
    have etaEmpty : hsame eta BHist.Empty :=
      hsame_trans (hsame_symm closed.right) leftEmpty
    have emptyComponent : NatTransPrefixComponentCarrier p q a BHist.Empty := by
      cases leftEmpty
      exact closed.left
    have identityData :=
      Iff.mp NatTransPrefixComponentCarrier_empty_identity_iff emptyComponent
    exact And.intro etaEmpty identityData.right.right.right
  · intro data
    cases data.left
    exact cont_left_unit_result leftRel

theorem NatTransPrefixComponentCarrier_vert_comp_identity_square_empty_result_iff
    {p q a eta left right : BHist} :
    NatTransPrefixComponentCarrier p q a eta -> Cont BHist.Empty eta left ->
      Cont eta BHist.Empty right ->
        (hsame left BHist.Empty ∧ hsame right BHist.Empty ↔
          hsame eta BHist.Empty ∧ hsame p q) := by
  intro component leftRel rightRel
  constructor
  · intro emptySquare
    exact
      (NatTransPrefixComponentCarrier_vert_comp_left_identity_empty_result_iff
        component leftRel).mp emptySquare.left
  · intro data
    exact
      And.intro
        ((NatTransPrefixComponentCarrier_vert_comp_left_identity_empty_result_iff
          component leftRel).mpr data)
        ((NatTransPrefixComponentCarrier_vert_comp_right_identity_empty_result_iff
          component rightRel).mpr data)

end BEDC.Derived.NatTransUp
