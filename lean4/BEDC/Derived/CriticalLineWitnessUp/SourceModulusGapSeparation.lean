import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_modulus_gap_separation
    {Z S M R Q H C P N sourceRead comparison gapRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R comparison ->
          Cont sourceRead comparison gapRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory sourceRead ∧ UnaryHistory comparison ∧
                UnaryHistory gapRead ∧ hsame comparison Q ∧ hsame H (append Z S) ∧
                  Cont Z S sourceRead ∧ Cont M R Q ∧ Cont M R comparison ∧
                    Cont sourceRead comparison gapRead ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sourceRoute comparisonRoute gapRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed sourceUnary comparisonUnary gapRoute
  have sameComparison : hsame comparison Q :=
    cont_deterministic comparisonRoute routeQ
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, sourceUnary, comparisonUnary, gapUnary,
      sameComparison, sameH, sourceRoute, routeQ, comparisonRoute, gapRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
