import BEDC.Derived.SternBrocotApproximationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SternBrocotApproximationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SternBrocotApproximationCarrier_finite_rational_bracketing
    (L U M T W R E H C P N bracketRead toleranceRead : BHist) :
    sternBrocotApproximationFields (SternBrocotApproximationUp.mk L U M T W R E H C P N) =
        [L, U, M, T, W, R, E, H, C, P, N] ->
      Cont W M bracketRead ->
        Cont bracketRead T toleranceRead ->
          hsame bracketRead (append W M) ∧ hsame toleranceRead (append bracketRead T) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro _fieldsExact bracketRoute toleranceRoute
  exact ⟨bracketRoute, toleranceRoute⟩

end BEDC.Derived.SternBrocotApproximationUp
