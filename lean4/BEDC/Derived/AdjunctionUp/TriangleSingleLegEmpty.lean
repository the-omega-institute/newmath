import BEDC.Derived.AdjunctionUp
import BEDC.Derived.NatTransUp.EmptyComponentPrefix

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.NatTransUp

theorem AdjunctionTriangleCarrier_single_leg_empty_iff
    {left right object unit counit leftLeg rightLeg : BHist} :
    AdjunctionTriangleCarrier left right object unit counit leftLeg rightLeg ->
      (hsame leftLeg BHist.Empty ↔ hsame rightLeg BHist.Empty) := by
  intro carrier
  constructor
  · intro leftEmpty
    have componentEmpty : unit = BHist.Empty ∧ counit = BHist.Empty := by
      cases leftEmpty
      exact cont_empty_result_inversion carrier.right.right.left
    have unitEmpty : hsame unit BHist.Empty := by
      cases componentEmpty.left
      exact hsame_refl BHist.Empty
    have counitEmpty : hsame counit BHist.Empty := by
      cases componentEmpty.right
      exact hsame_refl BHist.Empty
    exact cont_respects_hsame counitEmpty unitEmpty carrier.right.right.right
      (cont_right_unit BHist.Empty)
  · intro rightEmpty
    have componentEmpty : counit = BHist.Empty ∧ unit = BHist.Empty := by
      cases rightEmpty
      exact cont_empty_result_inversion carrier.right.right.right
    have counitEmpty : hsame counit BHist.Empty := by
      cases componentEmpty.left
      exact hsame_refl BHist.Empty
    have unitEmpty : hsame unit BHist.Empty := by
      cases componentEmpty.right
      exact hsame_refl BHist.Empty
    exact cont_respects_hsame unitEmpty counitEmpty carrier.right.right.left
      (cont_right_unit BHist.Empty)

theorem AdjunctionTriangleCarrier_single_boundary_total_collapse
    {left right object unit counit leftLeg rightLeg : BHist} :
    AdjunctionTriangleCarrier left right object unit counit leftLeg rightLeg ->
      (hsame unit BHist.Empty ∨ hsame counit BHist.Empty) ->
        hsame unit BHist.Empty ∧ hsame counit BHist.Empty ∧
          hsame leftLeg BHist.Empty ∧ hsame rightLeg BHist.Empty ∧ hsame left right := by
  intro carrier boundaryEmpty
  have componentEmpty : hsame unit BHist.Empty ∧ hsame counit BHist.Empty := by
    cases boundaryEmpty with
    | inl unitEmpty =>
        have sameLeftRight : hsame left right :=
          (NatTransPrefixComponentCarrier_component_empty_prefix_iff carrier.left).mp
            unitEmpty
        have sameRightLeft : hsame right left := hsame_symm sameLeftRight
        have counitEmpty : hsame counit BHist.Empty :=
          (NatTransPrefixComponentCarrier_component_empty_prefix_iff carrier.right.left).mpr
            sameRightLeft
        exact And.intro unitEmpty counitEmpty
    | inr counitEmpty =>
        have sameRightLeft : hsame right left :=
          (NatTransPrefixComponentCarrier_component_empty_prefix_iff carrier.right.left).mp
            counitEmpty
        have sameLeftRight : hsame left right := hsame_symm sameRightLeft
        have unitEmpty : hsame unit BHist.Empty :=
          (NatTransPrefixComponentCarrier_component_empty_prefix_iff carrier.left).mpr
            sameLeftRight
        exact And.intro unitEmpty counitEmpty
  have legsEmpty :=
    (AdjunctionTriangleCarrier_roundtrip_empty_iff_components_empty carrier).mpr
      componentEmpty
  have prefixesSame :=
    AdjunctionTriangleCarrier_empty_roundtrip_prefix_deterministic carrier
      legsEmpty.left legsEmpty.right
  exact And.intro componentEmpty.left
    (And.intro componentEmpty.right
      (And.intro legsEmpty.left (And.intro legsEmpty.right prefixesSame)))

end BEDC.Derived.AdjunctionUp
