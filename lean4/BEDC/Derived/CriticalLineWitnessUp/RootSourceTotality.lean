import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_source_totality
    {Z S M R Q H C P N sourceRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q sourceRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
          UnaryHistory Q ∧ UnaryHistory sourceRead ∧ hsame H (append Z S) ∧
            Cont M R Q ∧ Cont (append Z S) Q sourceRead ∧ Cont Q H C ∧
              Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet sourceRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryAppend unaryQ sourceRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, sourceUnary, sameH, routeQ, sourceRoute,
      routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
