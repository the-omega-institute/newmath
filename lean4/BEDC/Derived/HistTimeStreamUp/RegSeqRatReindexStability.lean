import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_regseqrat_reindex_stability [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name source' schedule' start' replay'
      transport' provenance' name' regseqRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      hsame source source' →
        hsame schedule schedule' →
          hsame start start' →
            hsame replay replay' →
              hsame transport transport' →
                hsame provenance provenance' →
                  hsame name name' →
                    Cont source' replay' regseqRead →
                      PkgSig bundle regseqRead pkg →
                        UnaryHistory source' ∧ UnaryHistory schedule' ∧ UnaryHistory start' ∧
                          UnaryHistory replay' ∧ UnaryHistory transport' ∧
                            UnaryHistory provenance' ∧ UnaryHistory name' ∧
                              UnaryHistory regseqRead ∧ Cont source' replay' regseqRead ∧
                                PkgSig bundle regseqRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier sameSource sameSchedule sameStart sameReplay sameTransport sameProvenance
    sameName sourceReplayRead readPkg
  obtain ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, transportUnary, provenanceUnary,
    nameUnary, _scheduleStartReplay, _sourceReplayProvenance, _provenanceReplay,
    _provenancePkg, _namePkg⟩ := carrier
  have sourceUnary' : UnaryHistory source' := unary_transport sourceUnary sameSource
  have scheduleUnary' : UnaryHistory schedule' := unary_transport scheduleUnary sameSchedule
  have startUnary' : UnaryHistory start' := unary_transport startUnary sameStart
  have replayUnary' : UnaryHistory replay' := unary_transport replayUnary sameReplay
  have transportUnary' : UnaryHistory transport' := unary_transport transportUnary sameTransport
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory name' := unary_transport nameUnary sameName
  have readUnary : UnaryHistory regseqRead :=
    unary_cont_closed sourceUnary' replayUnary' sourceReplayRead
  exact
    ⟨sourceUnary', scheduleUnary', startUnary', replayUnary', transportUnary',
      provenanceUnary', nameUnary', readUnary, sourceReplayRead, readPkg⟩

end BEDC.Derived.HistTimeStreamUp
