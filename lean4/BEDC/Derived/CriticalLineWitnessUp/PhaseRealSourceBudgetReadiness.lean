import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessPhaseRealSourceBudgetReadiness
    {Z S M R Q H C P N sourceBudget regseqRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont S M sourceBudget ->
        Cont sourceBudget R regseqRead ->
          Cont regseqRead Q refusalRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory sourceBudget ∧ UnaryHistory regseqRead ∧
                UnaryHistory refusalRead ∧ hsame H (append Z S) ∧ Cont S M sourceBudget ∧
                  Cont sourceBudget R regseqRead ∧ Cont regseqRead Q refusalRead ∧
                    Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier sourceBudgetRoute regseqRoute refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure carrier
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, _sameH, _routeQ, routeC, routeN⟩ :=
    carrier
  have sourceBudgetUnary : UnaryHistory sourceBudget :=
    unary_cont_closed unaryS unaryM sourceBudgetRoute
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed sourceBudgetUnary unaryR regseqRoute
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed regseqReadUnary routeClosure.left refusalRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, routeClosure.left, sourceBudgetUnary,
      regseqReadUnary, refusalReadUnary, routeClosure.right.right.right,
      sourceBudgetRoute, regseqRoute, refusalRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
