import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_route_transport_totality
    {Z S M R Q H C P N zeroRead replayRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont zeroRead H replayRead ->
          UnaryHistory zeroRead ∧ UnaryHistory replayRead ∧ hsame H (append Z S) ∧
            Cont Z S zeroRead ∧ Cont zeroRead H replayRead ∧ Cont M R Q ∧
              Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zeroRoute replayRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed zeroUnary unaryH replayRoute
  exact
    ⟨zeroUnary, replayUnary, sameH, zeroRoute, replayRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
