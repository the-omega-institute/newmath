import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_budget_source_totality
    {Z S M R Q H C P N budgetRead sourceRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R budgetRead ->
        Cont budgetRead H sourceRead ->
          UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧
            UnaryHistory budgetRead ∧ UnaryHistory sourceRead ∧ Cont M R Q ∧
              Cont M R budgetRead ∧ Cont budgetRead H sourceRead ∧
                hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet budgetRoute sourceRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have stripUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport stripUnary (hsame_symm sameH)
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed unaryM unaryR budgetRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed budgetUnary unaryH sourceRoute
  exact
    ⟨unaryM, unaryR, unaryQ, unaryH, budgetUnary, sourceUnary, routeQ, budgetRoute,
      sourceRoute, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
