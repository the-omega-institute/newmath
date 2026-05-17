import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_hsame_schedule_endpoint_transport [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name source' schedule' start' replay'
      transport' provenance' name' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      HistTimeStreamCarrier source' schedule' start' replay' transport' provenance' name'
          bundle pkg →
        hsame schedule schedule' →
          hsame start start' →
            Cont schedule start endpoint →
              Cont schedule' start' endpoint' →
                PkgSig bundle endpoint pkg →
                  hsame endpoint endpoint' ∧ UnaryHistory endpoint ∧
                    UnaryHistory endpoint' ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier carrier' scheduleSame startSame scheduleStartEndpoint
    schedule'Start'Endpoint' endpointPkg
  obtain ⟨_sourceUnary, scheduleUnary, startUnary, _replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  obtain ⟨_source'Unary, schedule'Unary, start'Unary, _replay'Unary, _transport'Unary,
    _provenance'Unary, _name'Unary, _schedule'Start'Replay', _source'Replay'Provenance',
    _provenance'Replay', _provenance'Pkg, _name'Pkg⟩ := carrier'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame scheduleSame startSame scheduleStartEndpoint schedule'Start'Endpoint'
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed scheduleUnary startUnary scheduleStartEndpoint
  have endpoint'Unary : UnaryHistory endpoint' :=
    unary_cont_closed schedule'Unary start'Unary schedule'Start'Endpoint'
  exact ⟨endpointSame, endpointUnary, endpoint'Unary, endpointPkg⟩

end BEDC.Derived.HistTimeStreamUp
