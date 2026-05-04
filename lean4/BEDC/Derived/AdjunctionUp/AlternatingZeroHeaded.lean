import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem AdjunctionUnitCounitCarrier_alternating_zero_headed_result_absurd
    {p q a unit counit left right depth z : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      UnaryHistory depth ->
        hsame (AdjunctionUnitCounitAlternating unit counit depth) (BHist.e0 z) -> False := by
  intro carrier depthUnary sameResult
  have unitUnary : UnaryHistory unit :=
    carrier.left.right.right.right.right.right.left
  have counitUnary : UnaryHistory counit :=
    carrier.right.left.right.right.right.right.right.left
  have resultUnary : UnaryHistory (AdjunctionUnitCounitAlternating unit counit depth) :=
    AdjunctionUnitCounitAlternating_unary unitUnary counitUnary depthUnary
  exact unary_no_zero_extension (unary_transport resultUnary sameResult)

end BEDC.Derived.AdjunctionUp
