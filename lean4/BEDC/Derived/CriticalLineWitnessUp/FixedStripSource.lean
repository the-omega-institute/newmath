import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def CriticalLineWitnessFixedStripSource (Z S M R Q H C P N : BHist) : Prop :=
  UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
    hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N

theorem CriticalLineWitnessFixedStripSource_carrier_route_closure
    {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessFixedStripSource Z S M R Q H C P N ->
      UnaryHistory P ->
        UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro source unaryP
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, sameH, routeQ, routeC, routeN⟩ := source
  have carrier : CriticalLineWitnessCarrier Z S M R Q H C P N :=
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩
  exact CriticalLineWitnessCarrier_modulus_route_closure carrier

end BEDC.Derived.CriticalLineWitnessUp
