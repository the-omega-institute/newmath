import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_cont_step_coverage [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name step : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont schedule start replay ->
        Cont schedule step replay ->
          PkgSig bundle provenance pkg ->
            UnaryHistory step ∧ hsame step start ∧ Cont schedule step replay ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier scheduleStartReplay scheduleStepReplay provenancePkg
  obtain ⟨_sourceUnary, _scheduleUnary, startUnary, _replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, _carrierScheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, _carrierProvenancePkg, _namePkg⟩ := carrier
  have sameStartStep : hsame start step :=
    cont_left_cancel scheduleStartReplay scheduleStepReplay
  have stepUnary : UnaryHistory step :=
    unary_transport startUnary sameStartStep
  exact
    ⟨stepUnary, hsame_symm sameStartStep, scheduleStepReplay, provenancePkg⟩

end BEDC.Derived.HistTimeStreamUp
