import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_classifier_separation
    {Z S M R Q H C P N zeroRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S zeroRead →
        Cont M R modulusRead →
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory zeroRead ∧
            UnaryHistory modulusRead ∧ hsame H (append Z S) ∧ Cont Z S zeroRead ∧
              Cont M R modulusRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zeroRoute modulusRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  exact
    ⟨unaryZ, unaryS, unaryM, zeroUnary, modulusUnary, sameH, zeroRoute, modulusRoute,
      routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
