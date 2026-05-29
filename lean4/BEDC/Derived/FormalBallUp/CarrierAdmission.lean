import BEDC.Derived.FormalBallUp

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_admission [AskSetup] [PackageSetup]
    {M R D W H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory W ∧
        PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: FormalBallCarrier BHist ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindow,
    _transportReplay, provenancePkg⟩ := carrier
  exact ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, provenancePkg⟩

end BEDC.Derived.FormalBallUp
