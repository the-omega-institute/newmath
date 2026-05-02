import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_zero_headed_component_absurd {source target morph : BHist} :
    CategoryHomCarrier source target morph →
      ((∃ z : BHist, source = BHist.e0 z) ∨ (∃ z : BHist, target = BHist.e0 z) ∨
        (∃ z : BHist, morph = BHist.e0 z)) → False := by
  intro homCarrier zeroComponent
  cases zeroComponent with
  | inl sourceZero =>
      cases sourceZero with
      | intro z sourceEq =>
          cases sourceEq
          exact unary_no_zero_extension homCarrier.left
  | inr rest =>
      cases rest with
      | inl targetZero =>
          cases targetZero with
          | intro z targetEq =>
              cases targetEq
              exact unary_no_zero_extension homCarrier.right.left
      | inr morphZero =>
          cases morphZero with
          | intro z morphEq =>
              cases morphEq
              exact unary_no_zero_extension homCarrier.right.right.left

end BEDC.Derived.CategoryUp
