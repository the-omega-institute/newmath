import BEDC.Derived.SequentiallyCompleteMetricUp.CauchySequenceObligation
import BEDC.Derived.SequentiallyCompleteMetricUp.ClassifierTransport
import BEDC.Derived.SequentiallyCompleteMetricUp.NameCertObligations

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricTailInduction [AskSetup] [PackageSetup]
    {X S M L D H C P N baseWindow stepWindow baseModulus stepModulus baseLimit
      stepLimit baseDistance stepDistance : BHist} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory S ->
          UnaryHistory M ->
            UnaryHistory L ->
              UnaryHistory D ->
                Cont X S baseWindow ->
                  Cont baseWindow M baseModulus ->
                    Cont baseModulus L baseLimit ->
                      Cont baseLimit D baseDistance ->
                        Cont baseDistance S stepWindow ->
                          Cont stepWindow M stepModulus ->
                            Cont stepModulus L stepLimit ->
                              Cont stepLimit D stepDistance ->
                                UnaryHistory baseDistance ∧ UnaryHistory stepDistance ∧
                                  Cont baseDistance S stepWindow ∧
                                    Cont stepLimit D stepDistance := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro fields xUnary sUnary mUnary lUnary dUnary baseWindowRoute baseModulusRoute
    baseLimitRoute baseDistanceRoute stepWindowRoute stepModulusRoute stepLimitRoute
    stepDistanceRoute
  have _acceptedFields :
      sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] := fields
  have baseWindowUnary : UnaryHistory baseWindow :=
    unary_cont_closed xUnary sUnary baseWindowRoute
  have baseModulusUnary : UnaryHistory baseModulus :=
    unary_cont_closed baseWindowUnary mUnary baseModulusRoute
  have baseLimitUnary : UnaryHistory baseLimit :=
    unary_cont_closed baseModulusUnary lUnary baseLimitRoute
  have baseDistanceUnary : UnaryHistory baseDistance :=
    unary_cont_closed baseLimitUnary dUnary baseDistanceRoute
  have stepWindowUnary : UnaryHistory stepWindow :=
    unary_cont_closed baseDistanceUnary sUnary stepWindowRoute
  have stepModulusUnary : UnaryHistory stepModulus :=
    unary_cont_closed stepWindowUnary mUnary stepModulusRoute
  have stepLimitUnary : UnaryHistory stepLimit :=
    unary_cont_closed stepModulusUnary lUnary stepLimitRoute
  have stepDistanceUnary : UnaryHistory stepDistance :=
    unary_cont_closed stepLimitUnary dUnary stepDistanceRoute
  exact ⟨baseDistanceUnary, stepDistanceUnary, stepWindowRoute, stepDistanceRoute⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
