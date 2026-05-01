import BEDC.FKernel.Bundle

namespace BEDC.FKernel.Bundle

theorem bundleAppend_common_context_cancel {PName : Type}
    {left middle right middle' : ProbeBundle PName} :
    bundleAppend left (bundleAppend middle right) =
      bundleAppend left (bundleAppend middle' right) ->
    middle = middle' := by
  intro same
  have innerSame : bundleAppend middle right = bundleAppend middle' right := by
    exact bundleAppend_prefix_cancel left (bundleAppend middle right)
      (bundleAppend middle' right) same
  exact bundleAppend_suffix_cancel middle middle' right innerSame

end BEDC.FKernel.Bundle
