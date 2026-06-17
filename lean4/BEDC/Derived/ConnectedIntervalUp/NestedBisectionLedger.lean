import BEDC.Derived.ConnectedIntervalUp

namespace BEDC.Derived.ConnectedIntervalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ConnectedIntervalCarrier_nested_bisection_ledger
    {L R W B S T E H C P N nestedRead realRead : BHist} :
    ConnectedIntervalCarrier L R W B S T E H C P N ->
      Cont B S nestedRead ->
        Cont nestedRead E realRead ->
          UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory B ∧
            UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory E ∧ UnaryHistory nestedRead ∧
              UnaryHistory realRead ∧ Cont L W B ∧ Cont B S T ∧ Cont B S nestedRead ∧
                Cont nestedRead E realRead ∧ Cont T E N ∧ Cont H C P := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ConnectedIntervalCarrier
  intro carrier nestedRoute realRoute
  obtain ⟨unaryL, unaryR, unaryW, unaryS, unaryE, routeB, routeT, routeN, routeP⟩ :=
    carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryL unaryW routeB
  have unaryT : UnaryHistory T :=
    unary_cont_closed unaryB unaryS routeT
  have nestedUnary : UnaryHistory nestedRead :=
    unary_cont_closed unaryB unaryS nestedRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed nestedUnary unaryE realRoute
  exact
    ⟨unaryL, unaryR, unaryW, unaryB, unaryS, unaryT, unaryE, nestedUnary, realUnary, routeB,
      routeT, nestedRoute, realRoute, routeN, routeP⟩

end BEDC.Derived.ConnectedIntervalUp
