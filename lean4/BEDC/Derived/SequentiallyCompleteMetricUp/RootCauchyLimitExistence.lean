import BEDC.Derived.SequentiallyCompleteMetricUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricRootCauchyLimitExistence [AskSetup] [PackageSetup]
    {X S M L D H C P N sequenceRead modulusRead limitRead distanceRead replayRead : BHist} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory S ->
          UnaryHistory M ->
            UnaryHistory L ->
              UnaryHistory D ->
                UnaryHistory C ->
                  Cont X S sequenceRead ->
                    Cont sequenceRead M modulusRead ->
                      Cont modulusRead L limitRead ->
                        Cont limitRead D distanceRead ->
                          Cont distanceRead C replayRead ->
                            UnaryHistory sequenceRead ∧ UnaryHistory modulusRead ∧
                              UnaryHistory limitRead ∧ UnaryHistory distanceRead ∧
                                UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro fields xUnary sUnary mUnary lUnary dUnary cUnary sequenceRoute modulusRoute limitRoute
    distanceRoute replayRoute
  have _acceptedFields :
      sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] := fields
  have sequenceUnary : UnaryHistory sequenceRead :=
    unary_cont_closed xUnary sUnary sequenceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sequenceUnary mUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary lUnary limitRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed limitUnary dUnary distanceRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed distanceUnary cUnary replayRoute
  exact ⟨sequenceUnary, modulusUnary, limitUnary, distanceUnary, replayUnary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
