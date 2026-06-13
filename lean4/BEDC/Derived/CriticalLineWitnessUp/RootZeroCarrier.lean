import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_zero_carrier
    {Z S M R Q H C P N rootRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S rootRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
          UnaryHistory Q ∧ UnaryHistory rootRead ∧ hsame H (append Z S) ∧
            Cont Z S rootRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame UnaryHistory
  intro packet rootRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed unaryZ unaryS rootRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, rootUnary, sameH, rootRoute, routeQ,
      routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
