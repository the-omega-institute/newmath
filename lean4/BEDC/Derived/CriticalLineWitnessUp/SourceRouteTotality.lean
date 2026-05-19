import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_route_totality
    {Z S M R Q H C P N sourceRead comparisonRead packageRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S sourceRead →
        Cont Q H comparisonRead →
          Cont C P packageRead →
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
                UnaryHistory N ∧ UnaryHistory sourceRead ∧ UnaryHistory comparisonRead ∧
                  UnaryHistory packageRead ∧ hsame H (append Z S) ∧
                    Cont Z S sourceRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                      Cont Q H comparisonRead ∧ Cont C P packageRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sourceRoute comparisonRoute packageRoute
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
  have unarySourceRead : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have unaryComparisonRead : UnaryHistory comparisonRead :=
    unary_cont_closed unaryQ unaryH comparisonRoute
  have unaryPackageRead : UnaryHistory packageRead :=
    unary_cont_closed unaryC unaryP packageRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryP, unaryN,
      unarySourceRead, unaryComparisonRead, unaryPackageRead, sameH, sourceRoute, routeQ,
      routeC, routeN, comparisonRoute, packageRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
