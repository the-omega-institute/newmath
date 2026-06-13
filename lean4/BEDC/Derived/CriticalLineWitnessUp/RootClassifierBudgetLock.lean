import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_classifier_budget_lock
    {Z S M R Q H C P N classifierRead budgetRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q H classifierRead ->
        Cont N Q budgetRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
              UnaryHistory classifierRead ∧ UnaryHistory budgetRead ∧
                hsame H (append Z S) ∧ Cont Q H classifierRead ∧
                  Cont N Q budgetRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet classifierRoute budgetRoute
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
  have unaryClassifierRead : UnaryHistory classifierRead :=
    unary_cont_closed unaryQ unaryH classifierRoute
  have unaryBudgetRead : UnaryHistory budgetRead :=
    unary_cont_closed unaryN unaryQ budgetRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN,
      unaryClassifierRead, unaryBudgetRead, sameH, classifierRoute, budgetRoute,
      routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
