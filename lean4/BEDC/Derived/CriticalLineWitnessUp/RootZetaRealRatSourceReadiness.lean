import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_zeta_real_rat_source_readiness
    {Z S M R Q H C P N zetaRead realRead ratRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) M zetaRead ->
        Cont M R realRead ->
          Cont R Q ratRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory zetaRead ∧ UnaryHistory realRead ∧
                UnaryHistory ratRead ∧ Cont (append Z S) M zetaRead ∧
                  Cont M R realRead ∧ Cont R Q ratRead ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro packet zetaRoute realRoute ratRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unarySource : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unarySource unaryM zetaRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed unaryM unaryR realRoute
  have ratUnary : UnaryHistory ratRead :=
    unary_cont_closed unaryR unaryQ ratRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, zetaUnary, realUnary, ratUnary,
      zetaRoute, realRoute, ratRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
