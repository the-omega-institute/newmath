import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_zero_modulus_carrier {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) ∧
          Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, routeClosure.left, routeClosure.right.left,
      routeClosure.right.right.left, sameH, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_root_zero_modulus_carrier_consumer_threshold
    {Z S M R Q H C P N thresholdRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R thresholdRead ->
        UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory thresholdRead ∧
          hsame H (append Z S) ∧ Cont M R Q ∧ Cont M R thresholdRead ∧ Cont Q H C ∧
            Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet thresholdRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryM unaryR thresholdRoute
  exact
    ⟨unaryM, unaryR, routeClosure.left, thresholdUnary, sameH, routeQ, thresholdRoute,
      routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
