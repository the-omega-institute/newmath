import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zeta_route_carrier_separation
    {Z S M R Q H C P N zetaRead stripRead comparisonRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont S M stripRead ->
          Cont zetaRead Q comparisonRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory zetaRead ∧
              UnaryHistory stripRead ∧ UnaryHistory comparisonRead ∧
                hsame H (append Z S) ∧ Cont Z S zetaRead ∧ Cont S M stripRead ∧
                  Cont zetaRead Q comparisonRead ∧ Cont M R Q ∧ Cont Q H C ∧
                    Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zetaRoute stripRoute comparisonRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZetaRead : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unaryStripRead : UnaryHistory stripRead :=
    unary_cont_closed unaryS unaryM stripRoute
  have unaryComparisonRead : UnaryHistory comparisonRead :=
    unary_cont_closed unaryZetaRead unaryQ comparisonRoute
  exact
    ⟨unaryZ, unaryS, unaryQ, unaryZetaRead, unaryStripRead, unaryComparisonRead, sameH,
      zetaRoute, stripRoute, comparisonRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
