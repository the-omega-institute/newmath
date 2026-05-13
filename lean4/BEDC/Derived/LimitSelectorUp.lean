import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.LimitSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

structure LimitSelectorCarrier : Type where
  regSeq : BHist
  precision : BHist
  modulus : BHist
  selectedIndex : BHist
  window : BHist
  dyadicReadback : BHist
  realSeal : BHist
  transports : BHist
  route : BHist
  provenance : BHist
  name : BHist
  selected_index_route : Cont precision modulus selectedIndex
  window_readback_route : Cont selectedIndex window dyadicReadback
  seal_route : Cont dyadicReadback realSeal route

theorem LimitSelectorCarrier_finite_witness_route (L : LimitSelectorCarrier) :
    Cont L.precision L.modulus L.selectedIndex ∧
      Cont L.selectedIndex L.window L.dyadicReadback ∧
        Cont L.dyadicReadback L.realSeal L.route := by
  exact ⟨L.selected_index_route, L.window_readback_route, L.seal_route⟩

end BEDC.Derived.LimitSelectorUp
