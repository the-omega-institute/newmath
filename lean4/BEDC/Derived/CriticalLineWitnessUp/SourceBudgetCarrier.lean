import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_budget_carrier
    {Z S M R Q H C P N sourceBudget : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceBudget ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
          UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
            UnaryHistory sourceBudget ∧ hsame H (append Z S) ∧
              Cont Z S sourceBudget ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet sourceRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unarySourceBudget : UnaryHistory sourceBudget :=
    unary_cont_closed unaryZ unaryS sourceRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN,
      unarySourceBudget, sameH, sourceRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
