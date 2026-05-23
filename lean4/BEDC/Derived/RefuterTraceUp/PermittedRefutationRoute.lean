import BEDC.Derived.RefuterTraceUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RefuterTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem RefuterTrace_permitted_refutation_route (r : RefuterTraceUp) :
    ∃ A U F E H C P N : BHist,
      r = RefuterTraceUp.mk A U F E H C P N ∧ Cont U F (append U F) ∧ hsame A A := by
  -- BEDC touchpoint anchor: BHist BMark
  cases r with
  | mk A U F E H C P N =>
      exact ⟨A, U, F, E, H, C, P, N, rfl, rfl, hsame_refl A⟩

end BEDC.Derived.RefuterTraceUp
