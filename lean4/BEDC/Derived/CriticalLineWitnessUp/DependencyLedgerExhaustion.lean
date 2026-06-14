import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_dependency_ledger_exhaustion
    {Z S M R Q H C P N zetaRead gammaRead dependencyRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont M R gammaRead ->
          Cont zetaRead gammaRead dependencyRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory zetaRead ∧ UnaryHistory gammaRead ∧
                UnaryHistory dependencyRead ∧ hsame H (append Z S) ∧
                  Cont Z S zetaRead ∧ Cont M R gammaRead ∧
                    Cont zetaRead gammaRead dependencyRead ∧ Cont Q H C ∧
                      Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet zetaRoute gammaRoute dependencyRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have gammaUnary : UnaryHistory gammaRead :=
    unary_cont_closed unaryM unaryR gammaRoute
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed zetaUnary gammaUnary dependencyRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, zetaUnary, gammaUnary, dependencyUnary,
      sameH, zetaRoute, gammaRoute, dependencyRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
