import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_refusal_totality
    {Z S M R Q H C P N refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N -> Cont N Q refusalRead ->
      UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory P ∧ UnaryHistory Q ∧
        UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory refusalRead ∧
          hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
            Cont N Q refusalRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  exact
    ⟨unaryM, unaryR, unaryP, routeClosure.left, routeClosure.right.left,
      routeClosure.right.right.left, refusalUnary, sameH, routeQ, routeC, routeN,
      refusalRoute⟩

theorem CriticalLineWitnessCarrier_zero_strip_route_totality
    {Z S M R Q H C P N zeroRead downstreamRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N -> Cont Z S zeroRead ->
      Cont zeroRead Q downstreamRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
          UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory zeroRead ∧
            UnaryHistory downstreamRead ∧ hsame H (append Z S) ∧ Cont Z S zeroRead ∧
              Cont zeroRead Q downstreamRead ∧ Cont M R Q ∧ Cont Q H C ∧
                Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zeroRoute downstreamRoute
  have routeClosure :
      UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) ∧
          Cont M R Q ∧ Cont Q H C ∧ Cont C P N :=
    CriticalLineWitnessCarrier_zero_strip_carrier_totality packet
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed routeClosure.left routeClosure.right.left zeroRoute
  have downstreamReadUnary : UnaryHistory downstreamRead :=
    unary_cont_closed zeroReadUnary routeClosure.right.right.right.right.left downstreamRoute
  exact
    ⟨routeClosure.left, routeClosure.right.left, routeClosure.right.right.left,
      routeClosure.right.right.right.left, routeClosure.right.right.right.right.left,
      routeClosure.right.right.right.right.right.left,
      routeClosure.right.right.right.right.right.right.left, zeroReadUnary, downstreamReadUnary,
      routeClosure.right.right.right.right.right.right.right.left, zeroRoute, downstreamRoute,
      routeClosure.right.right.right.right.right.right.right.right.left,
      routeClosure.right.right.right.right.right.right.right.right.right.left,
      routeClosure.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.CriticalLineWitnessUp
