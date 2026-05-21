import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_refusal_budget_completion
    {Z S M R Q H C P N rootRead rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q rootRead ->
        Cont rootRead N rhRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
            UnaryHistory rootRead ∧ UnaryHistory rhRead ∧ hsame H (append Z S) ∧
              Cont (append Z S) Q rootRead ∧ Cont rootRead N rhRead ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet rootRoute rhRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary routeClosure.left rootRoute
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed rootUnary routeClosure.right.right.left rhRoute
  exact
    ⟨unaryZ, unaryS, routeClosure.left, routeClosure.right.right.left, rootUnary, rhUnary,
      routeClosure.right.right.right, rootRoute, rhRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
