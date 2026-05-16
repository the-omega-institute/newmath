import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_regseqrat_local_clock_separation [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name observation regseqRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont source replay observation ->
        Cont schedule transport regseqRead ->
          PkgSig bundle regseqRead pkg ->
            UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory start ∧
              UnaryHistory replay ∧ UnaryHistory transport ∧ UnaryHistory observation ∧
                UnaryHistory regseqRead ∧ Cont source replay observation ∧
                  Cont schedule transport regseqRead ∧ hsame provenance replay ∧
                    PkgSig bundle regseqRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont Pkg ProbeBundle
  intro carrier sourceReplayObservation scheduleTransportRegseq regseqPkg
  obtain ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, transportUnary,
    _provenanceUnary, _nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
    provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed sourceUnary replayUnary sourceReplayObservation
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed scheduleUnary transportUnary scheduleTransportRegseq
  exact
    ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, transportUnary, observationUnary,
      regseqUnary, sourceReplayObservation, scheduleTransportRegseq, provenanceReplay,
      regseqPkg⟩

end BEDC.Derived.HistTimeStreamUp
