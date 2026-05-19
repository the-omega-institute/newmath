import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_consumer_coverage
    {Z S M R Q H C P N sourceRead ledgerRead consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) M sourceRead ->
        Cont M R ledgerRead ->
          Cont ledgerRead Q consumerRead ->
            UnaryHistory sourceRead ∧ UnaryHistory ledgerRead ∧ UnaryHistory consumerRead ∧
              hsame H (append Z S) ∧ Cont (append Z S) M sourceRead ∧
                Cont M R ledgerRead ∧ Cont ledgerRead Q consumerRead ∧ Cont Q H C ∧
                  Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sourceRoute ledgerRoute consumerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unarySourceBase : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unarySourceBase unaryM sourceRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed unaryM unaryR ledgerRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerUnary unaryQ consumerRoute
  exact
    ⟨sourceUnary, ledgerUnary, consumerUnary, sameH, sourceRoute, ledgerRoute,
      consumerRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
