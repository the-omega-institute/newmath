import BEDC.Derived.FormalBallCompletionUp.TasteGate

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallRadiusRefinement [AskSetup] [PackageSetup]
    {M R D W H C P N refinedWindow : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont R D refinedWindow ->
        PkgSig bundle refinedWindow pkg ->
          UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory W ∧
            UnaryHistory refinedWindow ∧ PkgSig bundle P pkg ∧
              PkgSig bundle refinedWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier radiusDyadicRefinement refinedPkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindow,
    _transportReplay, provenancePkg⟩ := carrier
  have refinedUnary : UnaryHistory refinedWindow :=
    unary_cont_closed radiusUnary dyadicUnary radiusDyadicRefinement
  exact
    ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, refinedUnary, provenancePkg,
      refinedPkg⟩

end BEDC.Derived.FormalBallUp
