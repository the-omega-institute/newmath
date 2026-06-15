import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealityConstrainedTowerPacketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def RealityConstrainedTowerPacketCarrier
    (O S R E D L Q H C P N : BHist) : Prop :=
  UnaryHistory O ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory D ∧
    UnaryHistory L ∧ UnaryHistory Q ∧ UnaryHistory P ∧ hsame H (append O S) ∧
      Cont S R E ∧ Cont E D L ∧ Cont L Q C ∧ Cont C P N

theorem RealityConstrainedTowerPacketCarrier_route_closure
    {O S R E D L Q H C P N endpoint : BHist} :
    RealityConstrainedTowerPacketCarrier O S R E D L Q H C P N ->
      Cont N Q endpoint ->
        UnaryHistory O ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧
          UnaryHistory D ∧ UnaryHistory L ∧ UnaryHistory Q ∧ UnaryHistory C ∧
            UnaryHistory N ∧ UnaryHistory endpoint ∧ hsame H (append O S) ∧
              Cont S R E ∧ Cont E D L ∧ Cont L Q C ∧ Cont C P N ∧
                Cont N Q endpoint := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet endpointRoute
  obtain ⟨unaryO, unaryS, unaryR, unaryE, unaryD, unaryL, unaryQ, unaryP, sameH,
    routeE, routeL, routeC, routeN⟩ := packet
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryL unaryQ routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed unaryN unaryQ endpointRoute
  exact
    ⟨unaryO, unaryS, unaryR, unaryE, unaryD, unaryL, unaryQ, unaryC, unaryN,
      endpointUnary, sameH, routeE, routeL, routeC, routeN, endpointRoute⟩

end BEDC.Derived.RealityConstrainedTowerPacketUp
