import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

structure BishopRegularCauchyCofinalStabilityUp where
  sourceName : BHist
  cofinalSchedule : BHist
  dyadicBudget : BHist
  streamWindow : BHist
  interleavingRoute : BHist
  realSeal : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  localName : BHist
  schedule_replay : Cont sourceName cofinalSchedule streamWindow
  seal_replay : Cont interleavingRoute realSeal replay

end BEDC.Derived
