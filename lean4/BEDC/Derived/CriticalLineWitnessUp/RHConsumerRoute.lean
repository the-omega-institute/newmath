import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_consumer_route
    {Z S M R Q H C P N rhRead consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q rhRead ->
        Cont rhRead C consumerRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
            UnaryHistory rhRead ∧ UnaryHistory consumerRead ∧ hsame H (append Z S) ∧
              Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont N Q rhRead ∧
                Cont rhRead C consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet rhRoute consumerRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryRhRead : UnaryHistory rhRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left rhRoute
  have unaryConsumerRead : UnaryHistory consumerRead :=
    unary_cont_closed unaryRhRead routeClosure.right.left consumerRoute
  exact
    ⟨unaryZ, unaryS, routeClosure.left, routeClosure.right.right.left, unaryRhRead,
      unaryConsumerRead, routeClosure.right.right.right, routeQ, routeC, routeN, rhRoute,
      consumerRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
