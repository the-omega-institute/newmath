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

theorem SequentiallyCompleteMetricCauchyTailStability [AskSetup] [PackageSetup]
    {X S M L D H C P N tailRead boundRead replayRead : BHist} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory S -> UnaryHistory M -> UnaryHistory D -> UnaryHistory C ->
        Cont S M tailRead -> Cont tailRead D boundRead ->
          Cont boundRead C replayRead ->
            UnaryHistory tailRead ∧ UnaryHistory boundRead ∧ UnaryHistory replayRead ∧
              Cont S M tailRead ∧ Cont tailRead D boundRead ∧
                Cont boundRead C replayRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro fields sUnary mUnary dUnary cUnary tailRoute boundRoute replayRoute
  have _acceptedFields :
      sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] := fields
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sUnary mUnary tailRoute
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed tailUnary dUnary boundRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed boundUnary cUnary replayRoute
  exact ⟨tailUnary, boundUnary, replayUnary, tailRoute, boundRoute, replayRoute⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
