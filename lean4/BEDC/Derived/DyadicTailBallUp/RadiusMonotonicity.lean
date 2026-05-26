import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicTailBallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DyadicTailBallRadiusMonotonicity {D F refinedRoute refinedBall R : BHist} :
    UnaryHistory D ->
      UnaryHistory F ->
        UnaryHistory refinedBall ->
          Cont D F refinedRoute ->
            Cont refinedRoute refinedBall R ->
              UnaryHistory refinedRoute ∧ UnaryHistory R := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro dyadicUnary filterUnary refinedBallUnary routeRefinement radiusRoute
  have refinedRouteUnary : UnaryHistory refinedRoute :=
    unary_cont_closed dyadicUnary filterUnary routeRefinement
  have radiusUnary : UnaryHistory R :=
    unary_cont_closed refinedRouteUnary refinedBallUnary radiusRoute
  exact ⟨refinedRouteUnary, radiusUnary⟩

end BEDC.Derived.DyadicTailBallUp
