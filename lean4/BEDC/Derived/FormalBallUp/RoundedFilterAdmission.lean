import BEDC.Derived.FormalBallUp

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_rounded_filter_admission [AskSetup] [PackageSetup]
    {M R D W H C P N roundedBoundary admittedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont W C roundedBoundary ->
        Cont roundedBoundary H admittedRead ->
          PkgSig bundle admittedRead pkg ->
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory W ∧
              UnaryHistory roundedBoundary ∧ UnaryHistory admittedRead ∧
                Cont W C roundedBoundary ∧ Cont roundedBoundary H admittedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle admittedRead pkg := by
  -- BEDC touchpoint anchor: FormalBallCarrier BHist Cont UnaryHistory ProbeBundle Pkg
  intro carrier windowRounded roundedAdmitted admittedPkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, transportUnary,
    replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have roundedBoundaryUnary : UnaryHistory roundedBoundary :=
    unary_cont_closed windowUnary replayUnary windowRounded
  have admittedReadUnary : UnaryHistory admittedRead :=
    unary_cont_closed roundedBoundaryUnary transportUnary roundedAdmitted
  exact
    ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, roundedBoundaryUnary,
      admittedReadUnary, windowRounded, roundedAdmitted, provenancePkg, admittedPkg⟩

end BEDC.Derived.FormalBallUp
