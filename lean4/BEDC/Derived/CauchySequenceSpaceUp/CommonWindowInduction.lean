import BEDC.Derived.CauchySequenceSpaceUp

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_common_window_induction [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name baseWindow
      baseCompletion succWindow succCompletion handoff sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont family schedule baseWindow ->
        Cont baseWindow tolerance baseCompletion ->
          Cont baseCompletion schedule succWindow ->
            Cont succWindow tolerance succCompletion ->
              Cont route name handoff ->
                Cont handoff succCompletion sealRead ->
                  UnaryHistory baseWindow ∧ UnaryHistory baseCompletion ∧
                    UnaryHistory succWindow ∧ UnaryHistory succCompletion ∧
                      UnaryHistory handoff ∧ UnaryHistory sealRead ∧
                        hsame window baseWindow ∧ hsame completion baseCompletion ∧
                          Cont family schedule baseWindow ∧
                            Cont baseWindow tolerance baseCompletion ∧
                              Cont baseCompletion schedule succWindow ∧
                                Cont succWindow tolerance succCompletion ∧
                                  Cont route name handoff ∧
                                    Cont handoff succCompletion sealRead ∧
                                      PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier familyScheduleBase baseToleranceCompletion baseCompletionScheduleSucc
    succToleranceCompletion routeNameHandoff handoffSuccSeal
  obtain ⟨familyUnary, scheduleUnary, _windowUnary, toleranceUnary, completionUnary,
    _transportUnary, routeUnary, nameUnary, familyScheduleWindow, windowToleranceCompletion,
    _completionTransportRoute, routePkg, _namePkg⟩ := carrier
  have baseWindowUnary : UnaryHistory baseWindow :=
    unary_cont_closed familyUnary scheduleUnary familyScheduleBase
  have baseCompletionUnary : UnaryHistory baseCompletion :=
    unary_cont_closed baseWindowUnary toleranceUnary baseToleranceCompletion
  have succWindowUnary : UnaryHistory succWindow :=
    unary_cont_closed baseCompletionUnary scheduleUnary baseCompletionScheduleSucc
  have succCompletionUnary : UnaryHistory succCompletion :=
    unary_cont_closed succWindowUnary toleranceUnary succToleranceCompletion
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeUnary nameUnary routeNameHandoff
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary succCompletionUnary handoffSuccSeal
  have sameWindow : hsame window baseWindow :=
    cont_respects_hsame (hsame_refl family) (hsame_refl schedule) familyScheduleWindow
      familyScheduleBase
  have sameCompletion : hsame completion baseCompletion :=
    cont_respects_hsame sameWindow (hsame_refl tolerance) windowToleranceCompletion
      baseToleranceCompletion
  exact
    ⟨baseWindowUnary, baseCompletionUnary, succWindowUnary, succCompletionUnary,
      handoffUnary, sealReadUnary, sameWindow, sameCompletion, familyScheduleBase,
      baseToleranceCompletion, baseCompletionScheduleSucc, succToleranceCompletion,
      routeNameHandoff, handoffSuccSeal, routePkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
