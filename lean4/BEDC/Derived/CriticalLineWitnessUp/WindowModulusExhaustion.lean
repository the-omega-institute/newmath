import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_window_modulus_exhaustion
    {Z S M R Q H C P N sourceWindow zeroLocator : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont (append Z S) M sourceWindow →
        Cont sourceWindow N zeroLocator →
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory Q ∧
            UnaryHistory sourceWindow ∧ UnaryHistory zeroLocator ∧
              hsame H (append Z S) ∧ Cont M R Q ∧
                Cont (append Z S) M sourceWindow ∧ Cont sourceWindow N zeroLocator ∧
                  Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sourceWindowRoute zeroLocatorRoute
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
  have sourceWindowUnary : UnaryHistory sourceWindow :=
    unary_cont_closed unaryAppend unaryM sourceWindowRoute
  have zeroLocatorUnary : UnaryHistory zeroLocator :=
    unary_cont_closed sourceWindowUnary unaryN zeroLocatorRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryQ, sourceWindowUnary, zeroLocatorUnary, sameH, routeQ,
      sourceWindowRoute, zeroLocatorRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
