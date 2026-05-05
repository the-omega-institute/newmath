import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem AdjunctionUnitCounitAlternating_positive_tail_result_empty_components_empty
    {unit counit depth tail : BHist} :
    UnaryHistory depth -> depth = BHist.e1 tail -> UnaryHistory tail ->
      (hsame tail BHist.Empty -> False) ->
        hsame (AdjunctionUnitCounitAlternating unit counit depth) BHist.Empty ->
          hsame unit BHist.Empty ∧ hsame counit BHist.Empty := by
  intro _depthUnary depthEq tailUnary tailNonempty resultEmpty
  cases depthEq
  have resultParts :
      hsame unit BHist.Empty ∧
        hsame (AdjunctionUnitCounitAlternating counit unit tail) BHist.Empty :=
    append_eq_empty_iff.mp resultEmpty
  have counitEmpty : hsame counit BHist.Empty :=
    AdjunctionUnitCounitAlternating_positive_depth_result_empty_unit_empty
      (unit := counit) (counit := unit) tailUnary tailNonempty resultParts.right
  exact And.intro resultParts.left counitEmpty

end BEDC.Derived.AdjunctionUp
