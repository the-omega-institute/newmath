import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamTransportLock [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name endpoint transported replayed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont source replay endpoint ->
        hsame endpoint transported ->
          Cont transported schedule replayed ->
            PkgSig bundle replayed pkg ->
              UnaryHistory endpoint ∧ UnaryHistory transported ∧ UnaryHistory replayed ∧
                hsame endpoint provenance ∧ Cont source replay endpoint ∧
                  Cont transported schedule replayed ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle replayed pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier sourceReplayEndpoint endpointTransported transportedScheduleReplayed replayedPkg
  obtain ⟨sourceUnary, scheduleUnary, _startUnary, replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, _scheduleStartReplay, sourceReplayProvenance,
    _provenanceReplay, provenancePkg, _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sourceUnary replayUnary sourceReplayEndpoint
  have transportedUnary : UnaryHistory transported :=
    unary_transport endpointUnary endpointTransported
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed transportedUnary scheduleUnary transportedScheduleReplayed
  have endpointSameProvenance : hsame endpoint provenance :=
    cont_deterministic sourceReplayEndpoint sourceReplayProvenance
  exact
    ⟨endpointUnary, transportedUnary, replayedUnary, endpointSameProvenance,
      sourceReplayEndpoint, transportedScheduleReplayed, provenancePkg, replayedPkg⟩

end BEDC.Derived.HistTimeStreamUp
