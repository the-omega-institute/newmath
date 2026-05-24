import BEDC.Derived.ClosedBoundedIntervalNetUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ClosedBoundedIntervalNetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ClosedBoundedIntervalNetFiniteMeshCoverage
    (x : ClosedBoundedIntervalNetUp) :
    ∃ located mesh rationalCells dyadicRefinements centers coverage streamWindows
        regSeqReadback realSeal transport route provenance name meshRead coverRead : BHist,
      x = ClosedBoundedIntervalNetUp.mk located mesh rationalCells dyadicRefinements centers
          coverage streamWindows regSeqReadback realSeal transport route provenance name ∧
        closedBoundedIntervalNetFields x =
          [located, mesh, rationalCells, dyadicRefinements, centers, coverage, streamWindows,
            regSeqReadback, realSeal, transport, route, provenance, name] ∧
          Cont mesh dyadicRefinements meshRead ∧ Cont meshRead coverage coverRead := by
  -- BEDC touchpoint anchor: BHist Cont append
  cases x with
  | mk located mesh rationalCells dyadicRefinements centers coverage streamWindows
      regSeqReadback realSeal transport route provenance name =>
      exact
        ⟨located, mesh, rationalCells, dyadicRefinements, centers, coverage, streamWindows,
          regSeqReadback, realSeal, transport, route, provenance, name,
          append mesh dyadicRefinements, append (append mesh dyadicRefinements) coverage,
          rfl, rfl, rfl, rfl⟩

end BEDC.Derived.ClosedBoundedIntervalNetUp
