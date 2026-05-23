import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_terminal_zero_source_totality
    {Z S M R Q H C P N terminalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S terminalRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
          UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory terminalRead ∧
            hsame H (append Z S) ∧ Cont Z S terminalRead ∧ Cont M R Q ∧
              Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet terminalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unaryTerminalRead : UnaryHistory terminalRead :=
    unary_cont_closed unaryZ unaryS terminalRoute
  exact
    ⟨unaryZ, unaryS, unaryH, unaryC, unaryP, unaryN, unaryTerminalRead, sameH,
      terminalRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
