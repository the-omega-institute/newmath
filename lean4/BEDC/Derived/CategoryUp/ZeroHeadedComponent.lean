import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

theorem CategoryHomCarrier_comp_zero_result_absurd {a b c f g z : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g (BHist.e0 z) ->
      False := by
  intro left right comp
  have composite : CategoryHomCarrier a c (BHist.e0 z) :=
    CategoryHomCarrier_comp_closed left right comp
  exact unary_no_zero_extension composite.right.right.left

end BEDC.Derived.CategoryUp
