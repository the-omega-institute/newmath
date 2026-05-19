import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_transport_replay_obligation
    {Z S M R Q H C P N replay : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont H C replay →
        UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory replay ∧ hsame H (append Z S) ∧
          Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont H C replay := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet replayRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryReplay : UnaryHistory replay :=
    unary_cont_closed unaryH routeClosure.right.left replayRoute
  exact
    ⟨unaryH, routeClosure.right.left, unaryReplay, routeClosure.right.right.right, routeQ,
      routeC, routeN, replayRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
