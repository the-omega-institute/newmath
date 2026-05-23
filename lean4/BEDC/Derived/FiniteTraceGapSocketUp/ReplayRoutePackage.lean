import BEDC.Derived.FiniteTraceGapSocketUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.FiniteTraceGapSocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FiniteTraceGapSocket_replay_route_package (x : FiniteTraceGapSocketUp) :
    ∃ trace socket streamSchedule regseqReadback realSeal transports continuations provenance
        nameCert : BHist,
      x =
          FiniteTraceGapSocketUp.mk trace socket streamSchedule regseqReadback realSeal transports
            continuations provenance nameCert ∧
        Cont trace streamSchedule (append trace streamSchedule) ∧
          Cont (append trace streamSchedule) regseqReadback
            (append (append trace streamSchedule) regseqReadback) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk trace socket streamSchedule regseqReadback realSeal transports continuations provenance
      nameCert =>
      exact
        ⟨trace, socket, streamSchedule, regseqReadback, realSeal, transports, continuations,
          provenance, nameCert, rfl, rfl, rfl⟩

end BEDC.Derived.FiniteTraceGapSocketUp
