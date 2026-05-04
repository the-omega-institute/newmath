import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem AdjunctionTriangleCarrier_components_empty_prefix_deterministic
    {left right object unit counit leftLeg rightLeg : BHist} :
    AdjunctionTriangleCarrier left right object unit counit leftLeg rightLeg ->
      hsame unit BHist.Empty -> hsame counit BHist.Empty -> hsame left right := by
  intro carrier unitEmpty counitEmpty
  have leftLegEmpty : hsame leftLeg BHist.Empty :=
    cont_respects_hsame unitEmpty counitEmpty carrier.right.right.left
      (cont_right_unit BHist.Empty)
  have rightLegEmpty : hsame rightLeg BHist.Empty :=
    cont_respects_hsame counitEmpty unitEmpty carrier.right.right.right
      (cont_right_unit BHist.Empty)
  exact AdjunctionTriangleCarrier_empty_roundtrip_prefix_deterministic
    carrier leftLegEmpty rightLegEmpty

end BEDC.Derived.AdjunctionUp
