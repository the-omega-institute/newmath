import BEDC.Derived.FormalBallCompletionUp.TasteGate

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_center_radius_admission [AskSetup] [PackageSetup]
    {M R D W H C P N centerRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont M R centerRead ->
        Cont H C nameRead ->
          PkgSig bundle nameRead pkg ->
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory W ∧
              UnaryHistory centerRead ∧ UnaryHistory nameRead ∧ Cont M R centerRead ∧
                Cont H C nameRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle nameRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier centerRoute nameRoute namePkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, transportUnary,
    replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have centerReadUnary : UnaryHistory centerRead :=
    unary_cont_closed metricUnary radiusUnary centerRoute
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed transportUnary replayUnary nameRoute
  exact
    ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, centerReadUnary,
      nameReadUnary, centerRoute, nameRoute, provenancePkg, namePkg⟩

end BEDC.Derived.FormalBallUp
