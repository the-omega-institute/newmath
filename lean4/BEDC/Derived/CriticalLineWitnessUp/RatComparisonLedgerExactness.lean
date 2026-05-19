import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rat_comparison_ledger_exactness
    {Z S M R Q H C P N comparisonRead publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q H comparisonRead ->
        Cont comparisonRead C publicRead ->
          UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory comparisonRead ∧
            UnaryHistory publicRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧
              Cont Q H comparisonRead ∧ Cont comparisonRead C publicRead ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet comparisonRoute publicRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed routeClosure.left unaryH comparisonRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed comparisonUnary routeClosure.right.left publicRoute
  exact
    ⟨routeClosure.left, unaryH, routeClosure.right.left, comparisonUnary, publicUnary, sameH,
      routeQ, routeC, comparisonRoute, publicRoute, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
