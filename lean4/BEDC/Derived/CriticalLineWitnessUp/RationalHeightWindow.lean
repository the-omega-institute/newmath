import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rational_height_window
    {Z S M R Q H C P N heightWindow requestRead boundedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M Q heightWindow ->
        Cont Z S requestRead ->
          Cont heightWindow requestRead boundedRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory Q ∧
              UnaryHistory heightWindow ∧ UnaryHistory requestRead ∧
                UnaryHistory boundedRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                  Cont M Q heightWindow ∧ Cont Z S requestRead ∧
                    Cont heightWindow requestRead boundedRead ∧ Cont Q H C ∧
                      Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory CriticalLineWitnessCarrier
  intro packet heightRoute requestRoute boundedRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryHeight : UnaryHistory heightWindow :=
    unary_cont_closed unaryM unaryQ heightRoute
  have unaryRequest : UnaryHistory requestRead :=
    unary_cont_closed unaryZ unaryS requestRoute
  have unaryBounded : UnaryHistory boundedRead :=
    unary_cont_closed unaryHeight unaryRequest boundedRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryQ, unaryHeight, unaryRequest, unaryBounded, sameH,
      routeQ, heightRoute, requestRoute, boundedRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
