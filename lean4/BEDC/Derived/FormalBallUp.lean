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

theorem FormalBallCarrier_directed_radius_transport [AskSetup] [PackageSetup]
    {M R D W H C P N radiusRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont R D radiusRead ->
        Cont radiusRead C transportedRead ->
          PkgSig bundle transportedRead pkg ->
            UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory C ∧
              UnaryHistory radiusRead ∧ UnaryHistory transportedRead ∧
                Cont R D radiusRead ∧ Cont radiusRead C transportedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle transportedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier radiusRoute transportedRoute transportedPkg
  obtain ⟨_metricUnary, radiusUnary, dyadicUnary, _windowUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindow,
    _transportReplay, provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusUnary dyadicUnary radiusRoute
  have transportedReadUnary : UnaryHistory transportedRead :=
    unary_cont_closed radiusReadUnary replayUnary transportedRoute
  exact
    ⟨radiusUnary, dyadicUnary, replayUnary, radiusReadUnary, transportedReadUnary,
      radiusRoute, transportedRoute, provenancePkg, transportedPkg⟩

end BEDC.Derived.FormalBallUp
