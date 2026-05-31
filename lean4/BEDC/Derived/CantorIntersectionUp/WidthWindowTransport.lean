import BEDC.Derived.CantorIntersectionUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.CantorIntersectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem CantorIntersectionCarrier_width_window_transport
    (x : CantorIntersectionCarrier) :
    ∃ N W D E R H C P Q transportedWindow : BHist,
      x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
        Cont N W transportedWindow ∧ hsame transportedWindow (append N W) := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  cases x with
  | packet N W D E R H C P Q =>
      exact ⟨N, W, D, E, R, H, C, P, Q, append N W, rfl, rfl, rfl⟩

end BEDC.Derived.CantorIntersectionUp
