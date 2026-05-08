import BEDC.Derived.AxisZeckendorf.FullAxis

namespace BEDC.Derived.AxisZeckendorf.FullAxis

open BEDC.FKernel.Hist
open BEDC.Derived.AxisZeckendorf.Spine

theorem FullAxisSourceSpec_boundary_01_thread_separation {h : BHist} :
    FullAxisSourceSpec zeroSpinePrefixThread h ->
      hsame h (BHist.e1 (BHist.e0 BHist.Empty)) -> False := by
  intro sourceH sameBoundary
  have boundarySpine : ZeroSpine (BHist.e1 (BHist.e0 BHist.Empty)) :=
    zeroSpine_hsame_transport sourceH sameBoundary
  exact zeroSpine_no_e1_extension boundarySpine

end BEDC.Derived.AxisZeckendorf.FullAxis
