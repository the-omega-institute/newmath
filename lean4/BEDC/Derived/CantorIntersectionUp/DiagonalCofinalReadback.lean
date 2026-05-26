import BEDC.Derived.CantorIntersectionUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.CantorIntersectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem CantorIntersection_diagonal_cofinal_readback
    (x : CantorIntersectionCarrier) :
    ∃ N W D E R H C P Q selectedWindow selectedEndpoint regSeqRead realRead : BHist,
      x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
        Cont W D selectedWindow ∧
          Cont selectedWindow E selectedEndpoint ∧
            Cont selectedEndpoint R regSeqRead ∧
              Cont regSeqRead H realRead ∧ hsame realRead (append regSeqRead H) := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  cases x with
  | packet N W D E R H C P Q =>
      exact ⟨N, W, D, E, R, H, C, P, Q, append W D, append (append W D) E,
        append (append (append W D) E) R, append (append (append (append W D) E) R) H,
        rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.CantorIntersectionUp
