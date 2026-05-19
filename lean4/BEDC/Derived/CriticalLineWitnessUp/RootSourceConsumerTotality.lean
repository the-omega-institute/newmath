import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_source_consumer_totality
    {Z S M R Q H C P N sourceRead comparisonRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont Q H comparisonRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
            UnaryHistory sourceRead ∧ UnaryHistory comparisonRead ∧ hsame H (append Z S) ∧
              Cont Z S sourceRead ∧ Cont Q H comparisonRead ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet sourceRoute comparisonRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unarySourceRead : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have unaryComparisonRead : UnaryHistory comparisonRead :=
    unary_cont_closed unaryQ unaryH comparisonRoute
  exact
    ⟨unaryZ, unaryS, unaryQ, unaryH, unarySourceRead, unaryComparisonRead, sameH,
      sourceRoute, comparisonRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
