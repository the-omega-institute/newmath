import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

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

end BEDC.Derived.AdjunctionUp
