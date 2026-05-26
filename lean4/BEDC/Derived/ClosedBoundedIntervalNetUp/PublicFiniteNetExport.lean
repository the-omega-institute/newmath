import BEDC.Derived.ClosedBoundedIntervalNetUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ClosedBoundedIntervalNetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ClosedBoundedIntervalNetPublicFiniteNetExport
    (x : ClosedBoundedIntervalNetUp) :
    ∃ L M Q D Z F S R E H C P N compactUniform : BHist,
      x = ClosedBoundedIntervalNetUp.mk L M Q D Z F S R E H C P N ∧
        closedBoundedIntervalNetFields x = [L, M, Q, D, Z, F, S, R, E, H, C, P, N] ∧
          Cont E C compactUniform ∧
            closedBoundedIntervalNetToEventFlow x =
              List.map closedBoundedIntervalNetEncodeBHist
                [L, M, Q, D, Z, F, S, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont append
  cases x with
  | mk L M Q D Z F S R E H C P N =>
      exact ⟨L, M, Q, D, Z, F, S, R, E, H, C, P, N, append E C, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.ClosedBoundedIntervalNetUp
