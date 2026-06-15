import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessTerminalModulusComparisonScope
    {Z S M R Q H C P N comparison : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q comparison ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
          UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧
            UnaryHistory comparison ∧ hsame H (append Z S) ∧ Cont M R Q ∧
              Cont Q H C ∧ Cont C P N ∧ Cont N Q comparison := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier comparisonRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    carrier
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed unaryN unaryQ comparisonRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryC, unaryN, comparisonUnary, sameH,
      routeQ, routeC, routeN, comparisonRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
