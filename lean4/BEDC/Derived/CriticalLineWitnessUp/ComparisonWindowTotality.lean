import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_comparison_window_totality
    {Z S M R Q H C P N zeroStripRead depthRead comparisonRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont M R depthRead ->
          Cont depthRead Q comparisonRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory zeroStripRead ∧ UnaryHistory depthRead ∧
                UnaryHistory comparisonRead ∧ hsame H (append Z S) ∧
                  Cont Z S zeroStripRead ∧ Cont M R Q ∧ Cont M R depthRead ∧
                    Cont depthRead Q comparisonRead ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet zeroStripRoute depthRoute comparisonRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZeroStripRead : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have unaryDepthRead : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthRoute
  have unaryComparisonRead : UnaryHistory comparisonRead :=
    unary_cont_closed unaryDepthRead unaryQ comparisonRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryZeroStripRead, unaryDepthRead,
      unaryComparisonRead, sameH, zeroStripRoute, routeQ, depthRoute, comparisonRoute,
      routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
