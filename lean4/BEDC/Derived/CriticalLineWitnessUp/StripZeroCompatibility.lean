import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_strip_zero_compatibility
    {Z S M R Q H C P N zeroStripRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        hsame H zeroStripRead ∧ UnaryHistory zeroStripRead ∧ hsame H (append Z S) ∧
          Cont Z S zeroStripRead ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zeroStripRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, _routeQ, routeC, routeN⟩ :=
    packet
  have sameZeroStrip : hsame zeroStripRead (append Z S) :=
    cont_deterministic zeroStripRoute (cont_intro rfl)
  have sameHZeroStrip : hsame H zeroStripRead :=
    hsame_trans sameH (hsame_symm sameZeroStrip)
  have zeroStripUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  exact ⟨sameHZeroStrip, zeroStripUnary, sameH, zeroStripRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
