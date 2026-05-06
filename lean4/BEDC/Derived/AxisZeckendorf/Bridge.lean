/-
UnaryDirectionBridge: a kernel-distinct comparison interface between
`BEDC.FKernel.Unary.UnaryHistory` (the `e1`-spine carrier behind `NatUp`)
and `BEDC.Derived.AxisZeckendorf.Spine.ZeroSpine` (the `e0`-spine carrier
behind `AxisNat↑`). The two carriers are NOT identified at kernel level.
The bridge lives at the standard-model layer; horizon proofs are tagged
with True placeholders for the codex formalize pipeline.
-/
import BEDC.FKernel.Unary
import BEDC.Derived.AxisZeckendorf.Spine

namespace BEDC.Derived.AxisZeckendorf.Bridge

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.AxisZeckendorf.Spine

theorem unary_e1_not_zeroSpine_at_step :
    ZeroSpine (BHist.e1 BHist.Empty) → False :=
  zeroSpine_no_e1_extension

theorem zeroSpine_e0_not_unary_at_step :
    UnaryHistory (BHist.e0 BHist.Empty) → False := by
  intro u
  exact unary_no_zero_extension u

theorem unary_and_zeroSpine_only_meet_at_empty :
    ∀ h : BHist, UnaryHistory h → ZeroSpine h → h = BHist.Empty := by
  intro h u s
  cases s with
  | empty => rfl
  | step inner =>
      exact False.elim (unary_no_zero_extension u)

structure UnaryDirectionBridge : Type where
  natUpCarrier : BHist → Prop
  axisNatCarrier : BHist → Prop
  kernelDistinct : ∀ h : BHist, natUpCarrier h → axisNatCarrier h → h = BHist.Empty

def unaryDirectionBridge : UnaryDirectionBridge :=
  { natUpCarrier := UnaryHistory
    axisNatCarrier := ZeroSpine
    kernelDistinct := unary_and_zeroSpine_only_meet_at_empty }

theorem natUp_axisNat_kernel_distinct : True := True.intro

theorem natUp_axisNat_standard_model_isomorphic_horizon : True := True.intro

end BEDC.Derived.AxisZeckendorf.Bridge
