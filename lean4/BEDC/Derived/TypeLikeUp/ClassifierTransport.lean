import BEDC.FKernel.Hist
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Ask
import BEDC.FKernel.Package.Core

namespace BEDC.Derived.TypeLikeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.Ask
open BEDC.FKernel.Package

theorem TypeLikeClassifierTransport [AskSetup] [PackageSetup]
    {B F Q E H _C _P N endpoint transported : BHist} :
    UnaryHistory B -> UnaryHistory F -> UnaryHistory Q -> UnaryHistory E ->
      UnaryHistory H -> Cont B F Q -> Cont Q E endpoint ->
        Cont endpoint H transported -> hsame transported N ->
          UnaryHistory endpoint ∧ UnaryHistory transported ∧ Cont B F Q ∧
            Cont Q E endpoint ∧ Cont endpoint H transported ∧ hsame transported N := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame AskSetup PackageSetup
  intro baseUnary fiberUnary classifierUnary exactnessUnary handoffUnary baseFiberRoute
    endpointRoute transportRoute transportedName
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed classifierUnary exactnessUnary endpointRoute
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed endpointUnary handoffUnary transportRoute
  exact
    ⟨endpointUnary, transportedUnary, baseFiberRoute, endpointRoute, transportRoute,
      transportedName⟩

end BEDC.Derived.TypeLikeUp
