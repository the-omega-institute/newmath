import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rational_comparison_ledger_totality
    {Z S M R Q H C P N comparisonRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont R Q comparisonRead ->
        Cont comparisonRead C refusalRead ->
          UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory comparisonRead ∧
            UnaryHistory refusalRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
              Cont R Q comparisonRead ∧ Cont comparisonRead C refusalRead ∧ Cont Q H C ∧
                Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet comparisonRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryR unaryQ comparisonRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed comparisonUnary unaryC refusalRoute
  exact
    ⟨unaryR, unaryQ, comparisonUnary, refusalUnary, sameH, routeQ, comparisonRoute,
      refusalRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
