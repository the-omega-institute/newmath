import BEDC.Derived.ClosedBoundedIntervalNetUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ClosedBoundedIntervalNetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ClosedBoundedIntervalNetCellCenterReadback (x : ClosedBoundedIntervalNetUp) :
    ∃ L M Q D Z F S R E H C P N centerRead coverageRead windowRead readback : BHist,
      x = ClosedBoundedIntervalNetUp.mk L M Q D Z F S R E H C P N ∧
        closedBoundedIntervalNetFields x = [L, M, Q, D, Z, F, S, R, E, H, C, P, N] ∧
          Cont Q D centerRead ∧ Cont centerRead Z coverageRead ∧
            Cont coverageRead S windowRead ∧ Cont windowRead R readback := by
  -- BEDC touchpoint anchor: BHist Cont append ClosedBoundedIntervalNetUp
  cases x with
  | mk L M Q D Z F S R E H C P N =>
      exact
        ⟨L, M, Q, D, Z, F, S, R, E, H, C, P, N, append Q D, append (append Q D) Z,
          append (append (append Q D) Z) S, append (append (append (append Q D) Z) S) R,
          rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.ClosedBoundedIntervalNetUp
