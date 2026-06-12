import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_tuple_image_row
    {Z S M R Q H C P N image : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S image →
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory image ∧ hsame H (append Z S) ∧
          Cont Z S image ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet imageRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have imageUnary : UnaryHistory image :=
    unary_cont_closed unaryZ unaryS imageRoute
  exact ⟨unaryZ, unaryS, imageUnary, sameH, imageRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
