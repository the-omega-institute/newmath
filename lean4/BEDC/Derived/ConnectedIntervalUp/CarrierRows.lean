import BEDC.Derived.ConnectedIntervalUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConnectedIntervalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ConnectedIntervalCarrierRows {L R W B S T E H C P N : BHist} :
    ConnectedIntervalCarrier L R W B S T E H C P N ->
      UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory B ∧
        UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory E ∧ Cont L W B ∧
          Cont B S T ∧ Cont T E N ∧ Cont H C P := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier
  obtain ⟨unaryL, unaryR, unaryW, unaryS, unaryE, routeB, routeT, routeN, routeP⟩ :=
    carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryL unaryW routeB
  have unaryT : UnaryHistory T :=
    unary_cont_closed unaryB unaryS routeT
  exact
    ⟨unaryL, unaryR, unaryW, unaryB, unaryS, unaryT, unaryE, routeB, routeT, routeN,
      routeP⟩

end BEDC.Derived.ConnectedIntervalUp
