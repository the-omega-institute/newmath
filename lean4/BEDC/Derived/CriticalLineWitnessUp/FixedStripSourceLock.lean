import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_source_lock
    {Z S M R Q H C P N fixedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S fixedRead ->
        UnaryHistory fixedRead ∧ hsame H (append Z S) ∧ Cont Z S fixedRead ∧
          Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet fixedRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have fixedUnary : UnaryHistory fixedRead :=
    unary_cont_closed unaryZ unaryS fixedRoute
  exact ⟨fixedUnary, sameH, fixedRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
