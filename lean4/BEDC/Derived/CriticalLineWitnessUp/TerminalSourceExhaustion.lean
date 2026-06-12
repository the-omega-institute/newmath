import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessTerminalSourceExhaustion
    {Z S M R Q H C P N terminalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont H C terminalRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
          UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory terminalRead ∧
            hsame H (append Z S) ∧ Cont H C terminalRead ∧ Cont M R Q ∧
              Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory CriticalLineWitnessCarrier
  intro packet terminalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed unaryH routeClosure.right.left terminalRoute
  exact
    ⟨unaryZ, unaryS, unaryH, routeClosure.right.left, unaryP, routeClosure.right.right.left,
      terminalUnary, routeClosure.right.right.right, terminalRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_terminal_source_exhaustion
    {Z S M R Q H C P N sourceRead terminalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead H terminalRead ->
          UnaryHistory terminalRead ∧ hsame H (append Z S) ∧ Cont Z S sourceRead ∧
            Cont sourceRead H terminalRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet sourceRoute terminalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have appendUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have hUnary : UnaryHistory H :=
    unary_transport appendUnary (hsame_symm sameH)
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed sourceUnary hUnary terminalRoute
  exact
    ⟨terminalUnary, sameH, sourceRoute, terminalRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
