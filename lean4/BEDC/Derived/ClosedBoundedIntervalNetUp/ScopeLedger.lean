import BEDC.Derived.ClosedBoundedIntervalNetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedBoundedIntervalNetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ClosedBoundedIntervalNetScopeLedger (x : ClosedBoundedIntervalNetUp) : Prop :=
  -- BEDC touchpoint anchor: ClosedBoundedIntervalNetUp BHist Cont UnaryHistory hsame
  ∃ located mesh rationalCells dyadicRefinements centers coverage streamWindows
      regSeqReadback realSeal transport route provenance name : BHist,
    x =
        ClosedBoundedIntervalNetUp.mk located mesh rationalCells dyadicRefinements centers
          coverage streamWindows regSeqReadback realSeal transport route provenance name ∧
      closedBoundedIntervalNetFields x =
          [located, mesh, rationalCells, dyadicRefinements, centers, coverage, streamWindows,
            regSeqReadback, realSeal, transport, route, provenance, name] ∧
        UnaryHistory mesh ∧ Cont located mesh rationalCells ∧
          Cont rationalCells dyadicRefinements coverage ∧ hsame realSeal realSeal

end BEDC.Derived.ClosedBoundedIntervalNetUp
