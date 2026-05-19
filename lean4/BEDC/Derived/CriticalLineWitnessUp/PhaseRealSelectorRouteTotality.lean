import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_selector_route_totality
    {Z S M R Q H C P N selectorRead regSeqRead realRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q selectorRead ->
        Cont selectorRead R regSeqRead ->
          Cont regSeqRead C realRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
              UnaryHistory C ∧ UnaryHistory selectorRead ∧ UnaryHistory regSeqRead ∧
                UnaryHistory realRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N ∧ Cont (append Z S) Q selectorRead ∧
                    Cont selectorRead R regSeqRead ∧ Cont regSeqRead C realRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet selectorRoute regSeqRoute realRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed sourceUnary unaryQ selectorRoute
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed selectorUnary unaryR regSeqRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regSeqUnary unaryC realRoute
  exact
    ⟨unaryZ, unaryS, unaryQ, unaryH, unaryC, selectorUnary, regSeqUnary, realUnary, sameH,
      routeQ, routeC, routeN, selectorRoute, regSeqRoute, realRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
