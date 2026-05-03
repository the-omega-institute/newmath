import BEDC.FKernel.Sig.Generation

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem sameSig_bundleAppend_common_context_iff [AskSetup]
    {left middle right : ProbeBundle ProbeName} {D : BHist -> Prop} {h k : BHist}
    (leftPolicy : BundleAskPolicy left D) (rightPolicy : BundleAskPolicy right D)
    (dh : D h) (dk : D k) (leftSame : SameSig left h k)
    (rightSame : SameSig right h k) :
    (SameSig (bundleAppend left (bundleAppend middle right)) h k ↔
      SameSig middle h k) := by
  constructor
  · intro fullSame
    have middleRightSame : SameSig (bundleAppend middle right) h k :=
      ((sameSig_bundleAppend_residual_iff
        (left := left) (right := bundleAppend middle right) (D := D)
        (h := h) (k := k)).left leftPolicy dh dk leftSame).mp fullSame
    exact
      ((sameSig_bundleAppend_residual_iff
        (left := middle) (right := right) (D := D) (h := h) (k := k)).right
        rightPolicy dh dk rightSame).mp middleRightSame
  · intro middleSame
    have middleRightSame : SameSig (bundleAppend middle right) h k :=
      sameSig_bundleAppend_closure middleSame rightSame
    exact sameSig_bundleAppend_closure leftSame middleRightSame

end BEDC.FKernel.Sig
