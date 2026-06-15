import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_source_separation
    {Z S M R Q H C P N sourceRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory Q ∧
          UnaryHistory sourceRead ∧ hsame H (append Z S) ∧ Cont Z S sourceRead ∧
            Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet sourceRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryQ, sourceUnary, sameH, sourceRoute, routeQ, routeC,
      routeN⟩

theorem CriticalLineWitnessCarrier_root_zero_strip_route
    {Z S M R Q H C P N zeroRead routeRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont H C routeRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
            UnaryHistory zeroRead ∧ UnaryHistory routeRead ∧ hsame H (append Z S) ∧
              Cont Z S zeroRead ∧ Cont H C routeRead ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zeroRoute routeReadRoute
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
  have _unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed unaryH unaryC routeReadRoute
  exact
    ⟨unaryZ, unaryS, unaryH, unaryC, zeroUnary, routeReadUnary, sameH, zeroRoute,
      routeReadRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
