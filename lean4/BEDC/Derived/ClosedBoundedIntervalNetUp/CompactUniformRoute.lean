import BEDC.Derived.ClosedBoundedIntervalNetUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ClosedBoundedIntervalNetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ClosedBoundedIntervalNetCompactUniformRoute
    (x : ClosedBoundedIntervalNetUp) :
    ∃ L M Q D Z F S R E H C P N meshRead coverRead readback realRead compactRead : BHist,
      x = ClosedBoundedIntervalNetUp.mk L M Q D Z F S R E H C P N ∧
        closedBoundedIntervalNetFields x = [L, M, Q, D, Z, F, S, R, E, H, C, P, N] ∧
          Cont M D meshRead ∧ Cont meshRead F coverRead ∧ Cont S R readback ∧
            Cont readback E realRead ∧ Cont realRead C compactRead := by
  -- BEDC touchpoint anchor: BHist Cont append ClosedBoundedIntervalNetUp
  cases x with
  | mk L M Q D Z F S R E H C P N =>
      exact
        ⟨L, M, Q, D, Z, F, S, R, E, H, C, P, N, append M D, append (append M D) F,
          append S R, append (append S R) E, append (append (append S R) E) C, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.ClosedBoundedIntervalNetUp
