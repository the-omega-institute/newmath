import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.NatTransUp

theorem AdjunctionUnitCounitCarrier_alternating_positive_depth_empty_prefix_same
    {p q a unit counit left right depth : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      UnaryHistory depth -> (hsame depth BHist.Empty -> False) ->
        hsame (AdjunctionUnitCounitAlternating unit counit depth) BHist.Empty ->
          hsame p q := by
  intro carrier depthUnary depthNonempty alternatingEmpty
  have unitEmpty : hsame unit BHist.Empty :=
    AdjunctionUnitCounitAlternating_positive_depth_result_empty_unit_empty depthUnary
      depthNonempty alternatingEmpty
  have unitComponentEmpty : NatTransPrefixComponentCarrier p q a BHist.Empty := by
    cases unitEmpty
    exact carrier.left
  have unitData :=
    (NatTransPrefixComponentCarrier_empty_identity_iff (p := p) (q := q) (a := a)).mp
      unitComponentEmpty
  exact unitData.right.right.right

end BEDC.Derived.AdjunctionUp
