import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_obligation_ledger_exactness_row
    {Z S M R Q H C P N ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q ledgerRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
          UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
            UnaryHistory N ∧ UnaryHistory ledgerRead ∧ hsame H (append Z S) ∧
              Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont N Q ledgerRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet ledgerRoute
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
  have unaryLedgerRead : UnaryHistory ledgerRead :=
    unary_cont_closed unaryN unaryQ ledgerRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryP, unaryN,
      unaryLedgerRead, sameH, routeQ, routeC, routeN, ledgerRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
