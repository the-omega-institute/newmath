import BEDC.Derived.ClosedBoundedIntervalNetUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ClosedBoundedIntervalNetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ClosedBoundedIntervalNetLocatedEndpointStability
    (x : ClosedBoundedIntervalNetUp) :
    ∃ L M Q D Z F S R E H C P N endpointTransport endpointReplay : BHist,
      x = ClosedBoundedIntervalNetUp.mk L M Q D Z F S R E H C P N ∧
        closedBoundedIntervalNetFields x = [L, M, Q, D, Z, F, S, R, E, H, C, P, N] ∧
          Cont L H endpointTransport ∧
            Cont endpointTransport C endpointReplay ∧ hsame endpointReplay endpointReplay := by
  -- BEDC touchpoint anchor: BHist Cont hsame append ClosedBoundedIntervalNetUp
  cases x with
  | mk L M Q D Z F S R E H C P N =>
      exact
        ⟨L, M, Q, D, Z, F, S, R, E, H, C, P, N, append L H, append (append L H) C,
          rfl, rfl, rfl, rfl, hsame_refl (append (append L H) C)⟩

end BEDC.Derived.ClosedBoundedIntervalNetUp
