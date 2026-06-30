import BEDC.Derived.FinitePrefixStreamUp.NameCertObligations

namespace BEDC.Derived.FinitePrefixStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FinitePrefixStreamCarrier_observation_induction [AskSetup] [PackageSetup]
    {k W D R H C P N observed replay : BHist} :
    FinitePrefixStreamCarrier k W D R H C P N ->
      Cont k W observed ->
        Cont observed D replay ->
          UnaryHistory k ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory observed ∧
            UnaryHistory replay ∧ Cont k W observed ∧ Cont observed D replay := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory FinitePrefixStreamCarrier
  intro carrier observedRoute replayRoute
  obtain ⟨depthUnary, windowUnary, dyadicUnary, _regularUnary, _comparisonUnary,
    _nameUnary, _sameStructural, _handoffRoute, _replayRoute, _namedRoute⟩ := carrier
  have observedUnary : UnaryHistory observed :=
    unary_cont_closed depthUnary windowUnary observedRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed observedUnary dyadicUnary replayRoute
  exact
    ⟨depthUnary, windowUnary, dyadicUnary, observedUnary, replayUnary, observedRoute,
      replayRoute⟩

end BEDC.Derived.FinitePrefixStreamUp
