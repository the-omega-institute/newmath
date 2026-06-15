import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_ledger_entry
    {Z S M R Q H C P N modulusRead ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R modulusRead ->
        Cont modulusRead Q ledgerRead ->
          UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧
            UnaryHistory modulusRead ∧ UnaryHistory ledgerRead ∧ hsame H (append Z S) ∧
              Cont M R modulusRead ∧ Cont modulusRead Q ledgerRead ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet modulusRoute ledgerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed modulusUnary unaryQ ledgerRoute
  exact
    ⟨unaryM, unaryR, unaryQ, unaryH, modulusUnary, ledgerUnary, sameH, modulusRoute,
      ledgerRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
