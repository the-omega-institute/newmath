import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_scoped_source_lock {Z S M R Q H C P N scopedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S scopedRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory Q ∧
          UnaryHistory scopedRead ∧ hsame H (append Z S) ∧ Cont Z S scopedRead ∧
            Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet scopedRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed unaryZ unaryS scopedRoute
  exact
    ⟨unaryZ, unaryS, unaryR, unaryQ, scopedUnary, sameH, scopedRoute, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
