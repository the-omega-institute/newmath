import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.NatTransUp

theorem AdjunctionTriangleCarrier_roundtrip_total_collapse
    {left right object unit counit leftLeg rightLeg : BHist} :
    AdjunctionTriangleCarrier left right object unit counit leftLeg rightLeg ->
      hsame unit BHist.Empty ∧ hsame counit BHist.Empty ∧
        hsame leftLeg BHist.Empty ∧ hsame rightLeg BHist.Empty ∧ hsame left right := by
  intro carrier
  have leftCollapse :=
    AdjunctionPrefix_unit_counit_composite_empty carrier.left carrier.right.left
      carrier.right.right.left
  have rightCollapse :=
    AdjunctionPrefix_unit_counit_composite_empty carrier.right.left carrier.left
      carrier.right.right.right
  have readback :=
    AdjunctionTriangleCarrier_roundtrip_empty_component_prefix_readback carrier
      leftCollapse.right rightCollapse.right
  exact
    And.intro readback.left
      (And.intro readback.right.left
        (And.intro leftCollapse.right
          (And.intro rightCollapse.right readback.right.right)))

end BEDC.Derived.AdjunctionUp
