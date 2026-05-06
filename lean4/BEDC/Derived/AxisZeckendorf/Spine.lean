/-
ZeroSpine carrier: histories generated from `Empty` by repeated `e0`-extension.
Parallel to `BEDC.FKernel.Unary` (which is `e1`-spine), but kernel-distinct.
The bridge to `NatUp`'s `e1`-spine is provided in
`BEDC.Derived.AxisZeckendorf.Bridge`, not by kernel identification.
-/
import BEDC.FKernel.Hist

namespace BEDC.Derived.AxisZeckendorf.Spine

open BEDC.FKernel.Hist

inductive ZeroSpine : BHist → Prop where
  | empty : ZeroSpine BHist.Empty
  | step : ∀ {h : BHist}, ZeroSpine h → ZeroSpine (BHist.e0 h)

theorem zeroSpine_empty : ZeroSpine BHist.Empty := ZeroSpine.empty

theorem zeroSpine_e0_closed {h : BHist} :
    ZeroSpine h → ZeroSpine (BHist.e0 h) := ZeroSpine.step

theorem zeroSpine_no_e1_extension {h : BHist} :
    ZeroSpine (BHist.e1 h) → False := by
  intro spine; cases spine

theorem zeroSpine_e0_inversion {h : BHist} :
    ZeroSpine (BHist.e0 h) → ZeroSpine h := by
  intro spine
  cases spine with
  | step inner => exact inner

theorem zeroSpine_hsame_transport {h k : BHist} :
    ZeroSpine h → hsame h k → ZeroSpine k := by
  intro spine same
  have : h = k := same
  exact this ▸ spine

end BEDC.Derived.AxisZeckendorf.Spine
