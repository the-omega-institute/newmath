import BEDC.Derived.CantorIntersectionUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.CantorIntersectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem CantorIntersectionRegSeqRatHandoffExactness (x : CantorIntersectionCarrier) :
    ∃ N W D E R H C P Q selectedHandoff : BHist,
      x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
        Cont D E selectedHandoff ∧ Cont selectedHandoff R (append selectedHandoff R) ∧
          hsame (append selectedHandoff R) (append (append D E) R) := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  cases x with
  | packet N W D E R H C P Q =>
      exact ⟨N, W, D, E, R, H, C, P, Q, append D E, rfl, rfl, rfl, rfl⟩

theorem CantorIntersectionCarrier_regseqrat_handoff_exactness
    (x : CantorIntersectionCarrier) :
    ∃ N W D E R H C P Q regSeqRead realRead : BHist,
      x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
        Cont E R regSeqRead ∧
          Cont regSeqRead H realRead ∧
            hsame realRead (append regSeqRead H) := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  cases x with
  | packet N W D E R H C P Q =>
      exact ⟨N, W, D, E, R, H, C, P, Q, append E R, append (append E R) H,
        rfl, rfl, rfl, rfl⟩

end BEDC.Derived.CantorIntersectionUp
