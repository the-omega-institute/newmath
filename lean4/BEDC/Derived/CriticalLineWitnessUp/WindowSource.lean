import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def CriticalLineWitnessWindowSource (Z S M H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory H ∧ UnaryHistory C ∧
    UnaryHistory P ∧ UnaryHistory N ∧ hsame H (append Z S) ∧
      ∃ R Q : BHist, Cont M R Q ∧ Cont Q H C ∧ Cont C P N

theorem CriticalLineWitnessWindowSource_carrier_projection
    {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      CriticalLineWitnessWindowSource Z S M H C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport
      (unary_cont_closed unaryZ unaryS (cont_intro rfl))
      (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  exact
    ⟨unaryZ, unaryS, unaryM, unaryH, unaryC, unaryP, unaryN, sameH,
      ⟨R, Q, routeQ, routeC, routeN⟩⟩

end BEDC.Derived.CriticalLineWitnessUp
