import BEDC.Derived.CantorIntersectionUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.CantorIntersectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

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
