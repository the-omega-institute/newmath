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

theorem SequentiallyCompleteMetricLimitLedgerNonescape [AskSetup] [PackageSetup]
    {X S M L D H C P N sequenceRead modulusRead limitRead distanceRead replayRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X -> UnaryHistory S -> UnaryHistory M -> UnaryHistory L ->
        UnaryHistory D -> UnaryHistory C -> UnaryHistory N ->
          Cont X S sequenceRead -> Cont sequenceRead M modulusRead ->
            Cont modulusRead L limitRead -> Cont limitRead D distanceRead ->
              Cont distanceRead C replayRead -> Cont replayRead N namedRead ->
                PkgSig bundle P pkg -> PkgSig bundle N pkg ->
                  UnaryHistory L ∧ UnaryHistory D ∧ UnaryHistory distanceRead ∧
                    UnaryHistory replayRead ∧ UnaryHistory namedRead ∧
                      Cont limitRead D distanceRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro fieldRows xUnary sUnary mUnary lUnary dUnary cUnary nUnary sequenceRoute
    modulusRoute limitRoute distanceRoute replayRoute namedRoute provenancePkg namePkg
  cases fieldRows
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
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  exact
    ⟨lUnary, dUnary, distanceUnary, replayUnary, namedUnary, distanceRoute,
      provenancePkg, namePkg⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
