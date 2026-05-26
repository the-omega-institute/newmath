import BEDC.Derived.AdjunctionUp.TriangleTotalCollapse

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist

theorem AdjunctionUp_StdBridge {left right object unit counit leftLeg rightLeg : BHist} :
    AdjunctionTriangleCarrier left right object unit counit leftLeg rightLeg →
      hsame unit BHist.Empty ∧ hsame counit BHist.Empty ∧
        hsame leftLeg BHist.Empty ∧ hsame rightLeg BHist.Empty ∧ hsame left right ∧
          AdjunctionUnitCounitDisplaySame left right object unit counit leftLeg rightLeg
            left left object BHist.Empty BHist.Empty BHist.Empty BHist.Empty := by
  -- BEDC touchpoint anchor: BHist hsame AdjunctionTriangleCarrier
  intro carrier
  have collapse := AdjunctionTriangleCarrier_roundtrip_total_collapse carrier
  have display := AdjunctionTriangleCarrier_display_empty_normal_form carrier
  exact
    ⟨collapse.left, collapse.right.left, collapse.right.right.left,
      collapse.right.right.right.left, collapse.right.right.right.right, display⟩

end BEDC.Derived.AdjunctionUp
