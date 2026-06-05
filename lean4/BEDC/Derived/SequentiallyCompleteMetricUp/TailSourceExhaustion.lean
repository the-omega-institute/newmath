import BEDC.Derived.SequentiallyCompleteMetricUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricTailSourceExhaustion [AskSetup] [PackageSetup]
    {X S M L D H C P N metricRead regSeqRead modulusRead limitRead distanceRead
      replayRead namedRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory S ->
          UnaryHistory M ->
            UnaryHistory L ->
              UnaryHistory D ->
                  UnaryHistory C ->
                    UnaryHistory N ->
                    UnaryHistory P ->
                      Cont X S metricRead ->
                        Cont metricRead M regSeqRead ->
                          Cont regSeqRead L modulusRead ->
                            Cont modulusRead D limitRead ->
                              Cont limitRead D distanceRead ->
                                Cont distanceRead C replayRead ->
                                  Cont replayRead N namedRead ->
                                    Cont namedRead P completionRead ->
                                      PkgSig bundle P pkg ->
                                        PkgSig bundle N pkg ->
                                        UnaryHistory metricRead ∧
                                          UnaryHistory regSeqRead ∧
                                            UnaryHistory modulusRead ∧
                                              UnaryHistory limitRead ∧
                                                UnaryHistory distanceRead ∧
                                                  UnaryHistory replayRead ∧
                                                    UnaryHistory namedRead ∧
                                                      UnaryHistory completionRead ∧
                                                        Cont X S metricRead ∧
                                                          Cont metricRead M regSeqRead ∧
                                                            Cont regSeqRead L modulusRead ∧
                                                              Cont modulusRead D limitRead ∧
                                                                Cont limitRead D distanceRead ∧
                                                                  Cont distanceRead C replayRead ∧
                                                                    Cont replayRead N namedRead ∧
                                                                      Cont namedRead P completionRead ∧
                                                                        PkgSig bundle P pkg ∧
                                                                          PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro fieldRows xUnary sUnary mUnary lUnary dUnary cUnary nUnary pUnary metricRoute
    regSeqRoute modulusRoute limitRoute distanceRoute replayRoute namedRoute completionRoute
    provenancePkg namePkg
  cases fieldRows
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed xUnary sUnary metricRoute
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed metricUnary mUnary regSeqRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed regSeqUnary lUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary dUnary limitRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed limitUnary dUnary distanceRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed distanceUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed namedUnary pUnary completionRoute
  exact
    ⟨metricUnary, regSeqUnary, modulusUnary, limitUnary, distanceUnary, replayUnary,
      namedUnary, completionUnary, metricRoute, regSeqRoute, modulusRoute, limitRoute,
      distanceRoute, replayRoute, namedRoute, completionRoute, provenancePkg, namePkg⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
