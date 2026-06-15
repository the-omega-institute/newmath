import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_gap_consumer_nonescape
    {Z S M R Q H C P N gapRead consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M Q gapRead ->
        Cont gapRead S consumerRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory Q ∧
            UnaryHistory gapRead ∧ UnaryHistory consumerRead ∧ hsame H (append Z S) ∧
              Cont M Q gapRead ∧ Cont gapRead S consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet gapRoute consumerRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, _unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed unaryM routeClosure.left gapRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed gapUnary unaryS consumerRoute
  exact
    ⟨unaryZ, unaryS, unaryM, routeClosure.left, gapUnary, consumerUnary, sameH,
      gapRoute, consumerRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
