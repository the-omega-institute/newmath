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

theorem SequentiallyCompleteMetricCauchySequenceObligation [AskSetup] [PackageSetup]
    {X S M L D H C P N sequenceRead modulusRead : BHist} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X -> UnaryHistory S -> UnaryHistory M -> Cont X S sequenceRead ->
        Cont sequenceRead M modulusRead ->
          UnaryHistory sequenceRead ∧ UnaryHistory modulusRead ∧ Cont X S sequenceRead ∧
            Cont sequenceRead M modulusRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro fields xUnary sUnary mUnary sequenceRoute modulusRoute
  have _acceptedFields :
      sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] := fields
  have sequenceUnary : UnaryHistory sequenceRead :=
    unary_cont_closed xUnary sUnary sequenceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sequenceUnary mUnary modulusRoute
  exact ⟨sequenceUnary, modulusUnary, sequenceRoute, modulusRoute⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
