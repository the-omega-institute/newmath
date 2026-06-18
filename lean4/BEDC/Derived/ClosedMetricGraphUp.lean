import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

structure ClosedMetricGraphUp where
  sourceMetric : BHist
  targetMetric : BHist
  graphRow : BHist
  sourceWindow : BHist
  targetWindow : BHist
  regularReadback : BHist
  realSeal : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  localName : BHist

namespace ClosedMetricGraphUp

theorem ClosedMetricGraphCarrier_sequential_closure (G : ClosedMetricGraphUp) :
    ∃ graphReplay targetReplay : BHist,
      Cont G.graphRow G.sourceWindow graphReplay ∧
        Cont graphReplay G.targetWindow targetReplay ∧
        hsame G.localName G.localName ∧ hsame G.realSeal G.realSeal := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  exact
    ⟨append G.graphRow G.sourceWindow, append (append G.graphRow G.sourceWindow) G.targetWindow,
      rfl, rfl, hsame_refl G.localName, hsame_refl G.realSeal⟩

end ClosedMetricGraphUp

end BEDC.Derived
