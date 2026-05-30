import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicTailBallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DyadicTailBallMonotoneInclusion {D F B R refinedRead terminalRead : BHist} :
    UnaryHistory D →
      UnaryHistory F →
        UnaryHistory R →
          Cont D F refinedRead →
            hsame refinedRead B →
              Cont B R terminalRead →
                UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro dyadicUnary filterUnary consumerUnary refinedRoute sameBall terminalRoute
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed dyadicUnary filterUnary refinedRoute
  have ballUnary : UnaryHistory B :=
    unary_transport refinedUnary sameBall
  exact unary_cont_closed ballUnary consumerUnary terminalRoute

end BEDC.Derived.DyadicTailBallUp
