import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem strip_zero_boundary_critical_line_witness_carrier_projection
    {Z S M R Q H C P N stripRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory stripRead ∧ hsame H (append Z S) ∧
          Cont Z S stripRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet stripRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  exact ⟨unaryZ, unaryS, stripUnary, sameH, stripRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
