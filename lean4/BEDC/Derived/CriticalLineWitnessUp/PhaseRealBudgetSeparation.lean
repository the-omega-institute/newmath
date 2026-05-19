import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_regseqrat_real_budget_separation
    {Z S M R Q H C P N budgetRead realEndpoint : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q R budgetRead ->
        Cont budgetRead H realEndpoint ->
          UnaryHistory Q ∧ UnaryHistory R ∧ UnaryHistory budgetRead ∧
            UnaryHistory realEndpoint ∧ hsame H (append Z S) ∧ Cont M R Q ∧
              Cont Q R budgetRead ∧ Cont budgetRead H realEndpoint ∧ Cont Q H C ∧
                Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet budgetRoute endpointRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed routeClosure.left unaryR budgetRoute
  have endpointUnary : UnaryHistory realEndpoint :=
    unary_cont_closed budgetUnary unaryH endpointRoute
  exact
    ⟨routeClosure.left, unaryR, budgetUnary, endpointUnary, routeClosure.right.right.right,
      routeQ, budgetRoute, endpointRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
