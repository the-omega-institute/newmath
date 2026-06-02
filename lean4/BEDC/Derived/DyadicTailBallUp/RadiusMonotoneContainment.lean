import BEDC.Derived.DyadicTailBallUp.MonotoneInclusion

namespace BEDC.Derived.DyadicTailBallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DyadicTailBallRadiusMonotoneContainment
    {D F B R refinedRead terminalRead containmentRead : BHist} :
    UnaryHistory D ->
      UnaryHistory F ->
        UnaryHistory R ->
          Cont D F refinedRead ->
            hsame refinedRead B ->
              Cont B R terminalRead ->
                Cont terminalRead R containmentRead ->
                  UnaryHistory terminalRead ∧ UnaryHistory containmentRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro dyadicUnary filterUnary consumerUnary refinedRoute sameBall terminalRoute containmentRoute
  have terminalUnary : UnaryHistory terminalRead :=
    DyadicTailBallMonotoneInclusion dyadicUnary filterUnary consumerUnary refinedRoute sameBall
      terminalRoute
  have containmentUnary : UnaryHistory containmentRead :=
    unary_cont_closed terminalUnary consumerUnary containmentRoute
  exact ⟨terminalUnary, containmentUnary⟩

end BEDC.Derived.DyadicTailBallUp
