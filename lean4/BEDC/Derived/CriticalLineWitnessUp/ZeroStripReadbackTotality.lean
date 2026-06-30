import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessZeroStripReadbackTotality
    {Z S M R Q H C P N stripRead comparisonRead readback : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q comparisonRead ->
          Cont comparisonRead N readback ->
            UnaryHistory stripRead ∧ UnaryHistory comparisonRead ∧ UnaryHistory readback ∧
              hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet stripRoute comparisonRoute readbackRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed stripUnary unaryQ comparisonRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed comparisonUnary unaryN readbackRoute
  exact ⟨stripUnary, comparisonUnary, readbackUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
