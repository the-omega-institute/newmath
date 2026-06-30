import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_terminal_nocompleteness_boundary
    {Z S M R Q H C P N phaseRead terminalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Q H phaseRead →
        Cont phaseRead N terminalRead →
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory phaseRead ∧ UnaryHistory terminalRead ∧
              hsame H (append Z S) ∧ Cont Q H phaseRead ∧
                Cont phaseRead N terminalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier phaseRoute terminalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure carrier
  obtain ⟨zUnary, sUnary, mUnary, rUnary, _pUnary, _sameH, _routeQ, _routeC, _routeN⟩ :=
    carrier
  have hUnary : UnaryHistory H :=
    unary_transport (unary_cont_closed zUnary sUnary (cont_intro rfl))
      (hsame_symm routeClosure.right.right.right)
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed routeClosure.left hUnary phaseRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed phaseUnary routeClosure.right.right.left terminalRoute
  exact
    ⟨zUnary, sUnary, mUnary, rUnary, routeClosure.left, phaseUnary, terminalUnary,
      routeClosure.right.right.right, phaseRoute, terminalRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
