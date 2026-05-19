import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_dependency_totality
    {Z S M R Q H C P N phaseRead realRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q phaseRead ->
        Cont phaseRead R realRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory Q ∧
            UnaryHistory H ∧ UnaryHistory phaseRead ∧ UnaryHistory realRead ∧
              hsame H (append Z S) ∧ Cont M R Q ∧ Cont (append Z S) Q phaseRead ∧
                Cont phaseRead R realRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet phaseRoute realRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed sourceUnary unaryQ phaseRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed phaseUnary unaryR realRoute
  exact
    ⟨unaryZ, unaryS, unaryR, unaryQ, unaryH, phaseUnary, realUnary, sameH, routeQ,
      phaseRoute, realRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
